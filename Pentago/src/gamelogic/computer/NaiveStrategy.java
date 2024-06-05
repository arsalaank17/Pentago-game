package gamelogic.computer;

import gamelogic.board.Board;
import gamelogic.player.Mark;
/**
 * Class for maintaining the Naive strategy for the Computer player in Pentago.
 * Module 2 project 2022 University of Twente
 * @author Kevin Schurman and Arsalaan Khan
 */
public class NaiveStrategy implements Strategy {

    /**
     * Returns the name of the strategy
     * @return the name of the strategy
     */
    //@ ensures \result != null;
    /*@ pure */
    @Override
    public String getName() {
        return "naive-computer";
    }

    /**
     * Determines the move for the computer player based on the naive strategy
     * In this case, the naive strategy is playing a random move anywhere
     * on the board
     * @param board the game board
     * @param mark the mark of the computer player
     * @return the computer player's chosen field
     */
    /*@ requires board != null && mark == Mark.BLACK || mark == Mark.WHITE;
        ensures board.isField(\result) && board.getField(\result) == Mark.EMPTY;
    */
    /*@ pure */
    @Override
    public int determineMove(Board board, Mark mark) {
        int rand;
        do {
            rand = (int) (Math.random() * (board.getTotal()));
        } while (!board.isEmptyField(rand));
        return rand;
    }
    /**
     * Determines the rotation for the computer player based on the naive strategy
     * In this case the strategy is to rotate randomly any board.
     * @param board the game board
     * @param mark the mark of the computer player
     * @return the computer player's chosen rotation
     */
    /*@ requires board != null && mark == Mark.BLACK || mark == Mark.WHITE;
        ensures board.isRotation(\result);
    */
    /*@ pure */
    @Override
    public int determineRotation(Board board, Mark mark) {
        return (int) (Math.random() * 7);
    }
}
