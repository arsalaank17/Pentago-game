package gamelogic.player;

import gamelogic.board.Board;
import gamelogic.computer.Strategy;

/**
 * Class for maintaining a Computer player in Pentago.
 * Module 2 project
 * @author Kevin Schurman and Arsalaan Khan
 */
public class ComputerPlayer extends Player {
    private final Strategy strategy;

    /**
     * Creates a new computer player object based on the strategy
     * given as the parameter
     * @param strategy Strategy that the computer will use against their opponent
     * @param mark Mark of the computers mark
     */
    /*@ requires strategy != null;
        requires mark == Mark.WHITE || mark == Mark.BLACK;
    */
    public ComputerPlayer(Strategy strategy, Mark mark) {
        super(strategy.getName(), mark);
        this.strategy = strategy;
    }

    /**
     * Determines the move for the computer player depending on the strategy chosen
     * @param board the game board
     * @return the computer player's chosen field
     */
    /*@ requires board != null;
        ensures board.isField(\result) && board.getField(\result) == Mark.EMPTY;
    */
    /*@ pure */
    @Override
    public int determineMove(Board board) {
        return strategy.determineMove(board, getMark());
    }

    /**
     * Determines the rotation for the computer player depending on the strategy
     * chosen
     * @param board the game board
     * @return the computer player's chosen rotation
     */
    /*@ requires board != null;
        ensures board.isRotation(\result);
    */
    /*@ pure */
    @Override
    public int determineRotation(Board board) {
        return strategy.determineRotation(board, getMark());
    }
}
