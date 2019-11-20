package markup;

import java.util.*;

public class Test {

    public static void main(String[] args) {
        OrderedList list = new OrderedList(List.of(
            new ListItem(new Paragraph(List.of(
                new Strong("1 "),
                new Text("2")
            ))),
            new ListItem(new UnorderedList(List.of(
                new ListItem(new Paragraph(List.of(
                    new Emphasis("Test "),
                    new Text("test")
                ))),
                new ListItem(new Paragraph(List.of(
                    new Emphasis("Test "),
                    new Strong("No "),
                    new Text("Text")
                )))
            ))),
            new ListItem(new OrderedList(List.of(
                new ListItem(new Paragraph(List.of(
                    new Emphasis("Emp "),
                    new Strong("Strong")
                )))
            )))
        ));
        StringBuilder sb = new StringBuilder();
        
        
        list.toTex(sb);
        System.out.println(sb.toString());

    }

}