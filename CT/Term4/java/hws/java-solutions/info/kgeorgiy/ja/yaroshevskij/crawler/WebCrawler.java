package info.kgeorgiy.ja.yaroshevskij.crawler;

import info.kgeorgiy.java.advanced.crawler.*;

import java.io.IOException;
import java.net.MalformedURLException;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.concurrent.*;

public class WebCrawler implements Crawler {

    final static String USAGE = "Usage: WebCrawler url [depth [downloads [extractors [perHost]]]]";
    final static int DEFAULT_DEPTH = 1;
    final static int DEFAULT_DOWNLOADERS = 1;
    final static int DEFAULT_EXTRACTORS = 1;
    final static int DEFAULT_PER_HOST = 1;

    private final int perHost;
    private final ExecutorService downloadWorkers;
    private final ExecutorService extractWorkers;
    private final Downloader downloader;
    private final Map<String, HostQueue> hostsQueues;

    public WebCrawler(Downloader downloader, int downloaders, int extractors, int perHost) {
        if (perHost < 1 || downloaders < 1 || extractors < 1) {
            throw new IllegalArgumentException("Connections per host, downloaders number, extractors number must " +
                    "greater than zero");
        }
        this.downloadWorkers = Executors.newFixedThreadPool(downloaders);
        this.extractWorkers = Executors.newFixedThreadPool(extractors);
        this.downloader = downloader;
        this.perHost = perHost;
        this.hostsQueues = new ConcurrentHashMap<>();
    }

    public static void main(String[] args) {
        if (args == null || args.length == 0 || args[0] == null) {
            System.err.println(USAGE);
            return;
        }
        try {
            String url = args[0];
            int depth = parseArgOrDefault(args, 1, DEFAULT_DEPTH);
            int downloaders = parseArgOrDefault(args, 2, DEFAULT_DOWNLOADERS);
            int extractors = parseArgOrDefault(args, 3, DEFAULT_EXTRACTORS);
            int perHost = parseArgOrDefault(args, 4, DEFAULT_PER_HOST);

            try (Crawler crawler = new WebCrawler(new CachingDownloader(), downloaders, extractors, perHost)) {
                crawler.download(url, depth);
            }
        } catch (NumberFormatException e) {
            System.err.println(USAGE);
            System.err.println("Cannot parse arguments: " + e.getMessage());
        } catch (IOException e) {
            System.err.println("Cannot create caching downloader: " + e.getMessage());
        }
    }

    private static int parseArgOrDefault(String[] args, int index, int defaultValue) {
        if (index < args.length) {
            return Integer.parseInt(args[index]);
        }
        return defaultValue;
    }

    @Override
    public Result download(String url, int maxDepth) {
        RecursiveDownloader recursiveDownloader = new RecursiveDownloader(maxDepth);
        return recursiveDownloader.run(url);
    }

    private void awaitServiceShutdow(ExecutorService service) {
        try {
            service.awaitTermination(1, TimeUnit.SECONDS);
        } catch (InterruptedException e) {
            // ignored
        } finally {
            service.shutdownNow();
        }
    }

    @Override
    public void close() {
        downloadWorkers.shutdown();
        extractWorkers.shutdown();
        awaitServiceShutdow(downloadWorkers);
        awaitServiceShutdow(extractWorkers);
    }

    private class RecursiveDownloader {
        private final Set<String> urls;
        private final Set<String> visited;
        private final Map<String, Integer> urlsDepths;
        private final Map<String, Document> urlsDocuments;
        private final Map<String, IOException> exceptions;
        private final int maxDepth;
        private final Phaser phaser;

        public RecursiveDownloader(int maxDepth) {
            this.urls = ConcurrentHashMap.newKeySet();
            this.visited = ConcurrentHashMap.newKeySet();
            this.urlsDepths = new ConcurrentHashMap<>();
            this.urlsDocuments = new ConcurrentHashMap<>();
            this.exceptions = new ConcurrentHashMap<>();
            this.phaser = new Phaser(1);
            this.maxDepth = maxDepth;
        }

        public Result run(final String url) {
            run(1, url);
            phaser.arriveAndAwaitAdvance();
            return new Result(List.copyOf(urls), exceptions);
        }

        private void run(final int depth, final String url) {
            if (!visited.contains(url) || urlsDepths.get(url) > depth) {
                urlsDepths.put(url, depth);
                try {
                    String host = URLUtils.getHost(url);
                    HostQueue hostQueue = hostsQueues.computeIfAbsent(host, s -> new HostQueue());

                    phaser.register();
                    hostQueue.add(() -> downloadTask(depth, url));
                } catch (MalformedURLException e) {
                    System.err.println("Cannot get hostname from url " + url + ": " + e.getMessage());
                }
            }
        }

        private void downloadTask(final int depth, final String url) {
            try {
                Document document;
                if (visited.add(url)) {
                    document = downloader.download(url);
                    urlsDocuments.put(url, document);
                } else {
                    document = urlsDocuments.get(url);
                }
                urls.add(url);
                if (depth < maxDepth) {
                    phaser.register();
                    extractWorkers.submit(() -> extractTask(depth, url, document));
                }
            } catch (IOException e) {
                exceptions.put(url, e);
            } finally {
                phaser.arrive();
            }
        }

        private void extractTask(final int depth, final String url, final Document document) {
            try {
                List<String> urls = document.extractLinks();
                urls.forEach(nextUrl -> run(depth + 1, nextUrl));
            } catch (IOException e) {
                System.err.println("Cannot extract links from " + url + ": " + e.getMessage());
            } finally {
                phaser.arrive();
            }
        }
    }

    private class HostQueue {
        Queue<Runnable> queue;
        Semaphore semaphore;

        HostQueue() {
            queue = new ConcurrentLinkedQueue<>();
            semaphore = new Semaphore(perHost);
        }

        public void add(Runnable task) {
            if (semaphore.tryAcquire()) {
                downloadWorkers.submit(() -> downloadTask(task));
            } else {
                queue.add(task);
            }
        }

        private void downloadTask(Runnable task) {
            task.run();
            if (!queue.isEmpty()) {
                Runnable newTask = queue.poll();
                if (newTask != null) {
                    downloadWorkers.submit(() -> downloadTask(newTask));
                } else {
                    semaphore.release();
                }
            } else {
                semaphore.release();
            }
        }
    }
}
