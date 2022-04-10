from math import log, exp
Q = 2
eps = 0.00001


def read_input():
    k = int(input())
    lambdas = list(map(int, input().split()))[:k]
    alpha = int(input())
    n = int(input())
    tr_classes = []
    tr_data = []
    class_count = [0 for _ in range(k)]
    words = set()
    for i in range(n):
        line = input().split()
        c = int(line[0])
        class_count[c - 1] += 1
        data = line[2:]
        tr_classes.append(c)
        tr_data.append(set(data))
        words.update(data)
    m = int(input())
    test_data = []
    for i in range(m):
        line = input().split()
        data = line[1:]
        test_data.append(set(data))
    words_in_class = calc_words_in_class(k, words, tr_data, tr_classes)
    print(words_in_class)
    print(class_count)
    p_w_c = [{word: (words_in_class[i][word] + alpha, class_count[i] + Q * alpha) for word in words} for i in range(k)]
    # p_c = [(0.01 if (class_count[i] == 0) else class_count[i], n) for i in range(k)]
    p_c = [(class_count[i], n) for i in range(k)]
    print(k)
    print(lambdas)
    print(words)
    print(p_c)
    print(p_w_c)
    print(m)
    print(test_data)
    exit()
    return k, lambdas, words, p_c, p_w_c, m, test_data


def calc_words_in_class(k, words, tr_data, tr_classes):
    words_in_class = [{word: 0 for word in words} for _ in range(k)]
    for i in range(len(tr_data)):
        data = tr_data[i]
        cur_class = tr_classes[i] - 1
        for word in data:
            words_in_class[cur_class][word] += 1
    return words_in_class


def get_result(k, lambdas, words, p_c, p_w_c, m, test_data):
    all_results = []
    for i in range(m):
        data = test_data[i]
        products = [log(p_c[j][0] + eps) - log(p_c[j][1] + eps) + log(lambdas[j] + eps) for j in range(k)]
        for j in range(k):
            for word in words:
                a, b = p_w_c[j][word]
                if data.__contains__(word):
                    products[j] += log(a + eps)
                    products[j] -= log(b + eps)
                else:
                    products[j] += log(b - a + eps)
                    products[j] -= log(b + eps)
        max_val = max(products)
        sum_products = max_val
        all_exp = list(map(lambda x: exp(x - max_val), products))
        sum_products += log(sum(all_exp) + eps)
        all_results.append(list(map(lambda x: exp(x - sum_products), products)))
    return all_results


def result_from_f(k, lambdas, alpha, n, tr_classes, tr_data_i, m, test_data_i):
    tr_data = []
    class_count = [0 for _ in range(k)]
    words = set()
    for i in range(n):
        c = tr_classes[i]
        class_count[c - 1] += 1
        data = set(tr_data_i[i])
        tr_data.append(data)
        words.update(data)
    test_data = []
    for i in range(m):
        test_data.append(set(test_data_i[i]))
    words_in_class = calc_words_in_class(k, words, tr_data, tr_classes)
    p_w_c = [{word: (words_in_class[i][word] + alpha, class_count[i] + Q * alpha) for word in words} for i in range(k)]
    p_c = [(0.01 if (class_count[i] == 0) else class_count[i], n) for i in range(k)]
    result = get_result(k, lambdas, words, p_c, p_w_c, m, test_data)
    return list(map(lambda x: find_max_pos(x, lambdas) + 1, result))


def result_from_f_with_p_1(k, lambdas, alpha, n, tr_classes, tr_data_i, m, test_data_i):
    tr_data = []
    class_count = [0 for _ in range(k)]
    words = set()
    for i in range(n):
        c = tr_classes[i]
        class_count[c - 1] += 1
        data = set(tr_data_i[i])
        tr_data.append(data)
        words.update(data)
    test_data = []
    for i in range(m):
        test_data.append(set(test_data_i[i]))
    words_in_class = calc_words_in_class(k, words, tr_data, tr_classes)
    p_w_c = [{word: (words_in_class[i][word] + alpha, class_count[i] + Q * alpha) for word in words} for i in range(k)]
    p_c = [(0.01 if (class_count[i] == 0) else class_count[i], n) for i in range(k)]
    result = get_result(k, lambdas, words, p_c, p_w_c, m, test_data)
    # print(result)
    return list(map(lambda x: (x[0], find_max_pos(x, lambdas) + 1), result))


def find_max_pos(data_list, lambdas):
    max_d = -1
    max_pos = -1
    for i in range(len(data_list)):
        if data_list[i] > max_d:
            max_d = data_list[i]
            max_pos = i
    if max_d == 0:
        return find_max_pos(lambdas, [1])
    return max_pos


if __name__ == '__main__':
    k, lambdas, words, p_c, p_w_c, m, test_data = read_input()
    all_results = get_result(k, lambdas, words, p_c, p_w_c, m, test_data)
    for res in all_results:
        print(*res, sep=" ")
