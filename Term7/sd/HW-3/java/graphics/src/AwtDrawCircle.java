import java.awt.*;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.awt.geom.Ellipse2D;

public class AwtDrawCircle extends Frame {

    @Override
    public void paint(Graphics g) {
        Graphics2D ga = (Graphics2D)g;
        ga.setPaint(Color.green);
        ga.fill(new Ellipse2D.Float(100.0f, 100.0f, 100.0f, 100.0f));
    }

    public static void main(String[] args) {
        Frame frame = new AwtDrawCircle();
        frame.addWindowListener(new WindowAdapter() {
            public void windowClosing(WindowEvent we) {
                System.exit(0);
            }
        });
        frame.setSize(600, 400);
        frame.setVisible(true);
    }
}
