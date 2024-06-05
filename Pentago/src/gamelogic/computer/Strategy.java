package gamelogic.computer;

import gamelogic.board.Board;
import gamelogic.player.Mark;

/**
 * Interface for maintaining the various strategies
 * of the computer player in Pentago game.
 * Module 2 Project 2022 University of Twente
 * @author Kevin Schurman and Arsalaan Khan
 */
public interface Strategy {

    /**
     * Returns the name of the strategy
     * @return the name of the strategy
     */
    //@ ensures \result != null;
    /*@ pure */
    String getName();

    /**
     * Determines the move for the computer player based on the strategy implemented
     * @param board the game board
     * @param mark the mark of the computer player
     * @return the computer player's chosen field
     */
    /*@ requires board != null && mark == Mark.BLACK || mark == Mark.WHITE;
        ensures board.isField(\result) && board.getField(\result) == Mark.EMPTY;
    @*/
    /*@ pure */
    int determineMove(Board board, Mark mark);

    /**
     * Determines the rotation for the computer player based on the strategy implemented
     * @param board the game board
     * @param mark the mark of the computer player
     * @return the computer player's chosen field
     */
    /*@ requires board != null && mark == Mark.BLACK || mark == Mark.WHITE;
        ensures board.isRotation(\result);
    */
    /*@ pure @*/
    int determineRotation(Board board, Mark mark);
}
