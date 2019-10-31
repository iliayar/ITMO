import java.util.ArrayList;;


public class Test {

    public void main(String[] args) {
        StringBuilder test = new StringBuilder();
        Paragraph paragraph = new Paragraph(List.of(
            new Strong(List.of(
                new Text("1"),
                new Strikeout(List.of(
                    new Text("2"),
                    new Emphasis(List.of(
                        new Text("3"),
                        new Text("4")
                    )),
                    new Text("5")
                )),
                new Text("6")
            ))
        ));
        paragraph.toMakdown(test);
        System.out.println(test.toString());
    }
}