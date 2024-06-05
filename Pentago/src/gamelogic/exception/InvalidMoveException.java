package gamelogic.exception;

public class InvalidMoveException extends RuntimeException {
    public InvalidMoveException(String str) {
        super(str);
    }
}
