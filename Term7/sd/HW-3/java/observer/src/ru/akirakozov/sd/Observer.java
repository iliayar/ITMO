package ru.akirakozov.sd;

/**
 * Example from:
 * https://www.tutorialspoint.com/design_pattern/observer_pattern.htm
 */
public abstract class Observer {
    protected Subject subject;
    public abstract void update();

    public static class BinaryObserver extends Observer{

        public BinaryObserver(Subject subject){
            this.subject = subject;
            this.subject.attach(this);
        }

        @Override
        public void update() {
            System.out.println( "Binary String: " + Integer.toBinaryString( subject.getState() ) );
        }
    }

    public static class OctalObserver extends Observer{

        public OctalObserver(Subject subject){
            this.subject = subject;
            this.subject.attach(this);
        }

        @Override
        public void update() {
            System.out.println( "Octal String: " + Integer.toOctalString(subject.getState()) );
        }
    }

    public static class HexaObserver extends Observer{

        public HexaObserver(Subject subject){
            this.subject = subject;
            this.subject.attach(this);
        }

        @Override
        public void update() {
            System.out.println( "Hex String: " + Integer.toHexString( subject.getState() ).toUpperCase() );
        }
    }
}