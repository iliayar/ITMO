package md2html;

import java.util.ArrayList;
import java.util.Arrays;

public class TokenStack {

    Token[] stack;
    int index;

    public TokenStack() {
        this.stack = new Token[16];
        index = 0;
    }

    private void expandToken() {
        stack = Arrays.copyOf(stack, stack.length*2);
    }

    public void push(Token t) {
        if(index >= stack.length) {
            expandToken();
        }
        stack[index++] = t;
    }

    public int getSize() {
        return index;
    }

    public Token pop() throws IndexOutOfBoundsException{
        if(index > 0) {
            return stack[--index];
        }
        throw new IndexOutOfBoundsException();
    }

    public void erase(int n) throws IndexOutOfBoundsException {
        for(int i = 0; i < n; ++i) {
            pop();
        }
    }

    public Token getFromEnd(int i) throws  IndexOutOfBoundsException {
        if(index - i - 1 >= 0) {
            return stack[index - i - 1];
        }
        throw new IndexOutOfBoundsException();
    }

    public Token getTop() throws IndexOutOfBoundsException {
        if(index >= 0) {
            return stack[index - 1];
        }
        throw new IndexOutOfBoundsException();
    }

    public ArrayList<Token> toArrayList() {
        ArrayList<Token> res = new ArrayList<Token>();
        for(int i = 0; i < index; ++i) {
            res.add(stack[i]);
        }
        return res;
    }
}
