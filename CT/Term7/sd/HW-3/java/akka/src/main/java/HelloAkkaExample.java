import akka.actor.ActorRef;
import akka.actor.ActorSystem;
import akka.actor.Props;
import akka.actor.UntypedActor;

/**
 * @author akirakozov
 */
public class HelloAkkaExample {

    public static class Name {
        public final String name;

        public Name(String name) {
            this.name = name;
        }
    }

    public static class HelloActor extends UntypedActor {

        @Override
        public void onReceive(Object message) throws Throwable {
            if (message instanceof Name) {
                System.out.println("Hello, " + ((Name) message).name);
            }
        }
    }

    public static void main(String[] args) {
        ActorSystem system = ActorSystem.create("MySystem");
        // Create actor
        ActorRef actor = system.actorOf(
                Props.create(HelloActor.class), "helloActor");

        // Send message
        actor.tell(new Name("Petr"), ActorRef.noSender());
    }


}
