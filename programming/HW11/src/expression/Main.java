package expression;

public class Main {


    private void run(String[] argv) {
        Expression e = new Divide(new Variable("x"), new Const(-2));
        System.out.println(e.evaluate(2));
        System.out.println(e.toMiniString());


        System.out.println(new Add(new Variable("x"), new Variable("x")).equals(new Add(new Variable("x"), new Variable("x"))));
    }

    public static void main(String[] argv) {
        new Main().run(argv);
    }

}
