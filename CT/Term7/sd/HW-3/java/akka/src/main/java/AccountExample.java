import akka.actor.ActorRef;
import akka.actor.ActorSystem;
import akka.actor.Props;
import akka.actor.UntypedActor;

/**
 * @author akirakozov
 */
public class AccountExample {

    public static class Withdrawal {
        public final int amount;

        public Withdrawal(int amount) {
            this.amount = amount;
        }
    }

    public static class AccountActor extends UntypedActor {
        int balance = 100;

        @Override
        public void onReceive(Object message) throws Throwable {
            if (message instanceof  Withdrawal) {
                int amount = ((Withdrawal) message).amount;
                if (balance >= amount) {
                    balance -= amount;
                    sender().tell(true, self());
                } else {
                    sender().tell(false, self());
                }
            }
        }
    }


    public static void main(String[] args) {
        ActorSystem system = ActorSystem.create("MySystem");
        ActorRef actor = system.actorOf(Props.create(AccountActor.class), "account");

        actor.tell(new Withdrawal(20), null);
    }
}
