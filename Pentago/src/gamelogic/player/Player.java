package gamelogic.player;

import gamelogic.board.Board;

/**
 * Abstract class for keeping a player in the Pentago game. Module 2
 * project
 * @author Arsalaan Khan and Kevin Schurman
 */
public abstract class Player {
    private final String name;
    private final Mark mark;

    /**
     * Creates a new Player object.
     * @param name String of the players name.
     * @param mark Mark of the players mark
     */
    /*@ requires name != null;
        requires mark == Mark.WHITE || mark == Mark.BLACK;
        ensures this.name == name;
        ensures this.mark == mark;
    @*/
    public Player(String name, Mark mark) {
        this.name = name;
        this.mark = mark;
    }
    /**
     * Returns the name of the player.
     * @return String of the players name
     */
    /*@ pure */
    public String getName() {
        return name;
    }

    /**
     * Returns the mark of the player.
     * @return mark of the player
     */
    /*@ pure */
    public Mark getMark() {
        return mark;
    }

    /**
     * Determines the field for the next move.
     * @param board the current game board
     * @return the player's choice
     */
    /*@ requires board != null && board.isFull() == false;
        ensures board.isField(\result) && board.getField(\result) == Mark.EMPTY;
    @*/
    public abstract int determineMove(Board board);

    /**
     * Determines the rotation number for the move.
     * @param board the game board
     * @return the player's chosen field
     */
    /*@ requires board != null;
        ensures board.isRotation(\result);
    @*/
    public abstract int determineRotation(Board board);

    /**
     * Makes a move on the board.
     * @param board the current board
     * @return int where the player will make the move
     */
    //@ requires board != null && board.isFull() == false;
    public int makeMove(Board board) {
        int move;
        do {
            move = determineMove(board.deepCopy());
        } while (!(board.isField(move) && board.isEmptyField(move)));
        return move;
    }

    /**
     * Makes the rotation on the board after the marble has been placed.
     * @param board the current board
     * @return int of the current move the player has made
     */
    //@ requires board != null;
    public int makeRotate(Board board) {
        int move;
        do {
            move = determineRotation(board.deepCopy());
        } while (!board.isRotation(move));
        return move;
    }
}
