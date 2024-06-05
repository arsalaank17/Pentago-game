package gamelogic.computer;

import gamelogic.board.Board;
import gamelogic.player.Mark;

import java.util.ArrayList;
import java.util.List;

/**
 * Class for maintaining the smart strategy for the Computer player in Pentago.
 * Module 2 project 2022 University of Twente
 * @author Kevin Schurman and Arsalaan Khan
 */
public class SmartStrategy implements Strategy {

    /**
     * Returns the name of the strategy
     * @return the name of the strategy
     */
    //@ ensures \result != null;
    /*@ pure */
    @Override
    public String getName() {
        return "smart-computer";
    }

    /**
     * Determines the move for the computer player based on the smart strategy
     * In this case, the smart strategy is checking for winning condition before playing
     * the move
     * @param board the game board
     * @param mark the mark of the computer player
     * @return the computer player's chosen field
     */
    /*@ requires board != null && mark == Mark.BLACK || mark == Mark.WHITE;
        ensures board.isField(\result) && board.getField(\result) == Mark.EMPTY;
    @*/
    /*@ pure */
    @Override
    public int determineMove(Board board, Mark mark) {
        Board temp = board.deepCopy();
        Mark[] fields = {mark, mark == Mark.BLACK ? Mark.WHITE : Mark.BLACK};
        List<Integer[]> counts = new ArrayList<>();
        for (int j = 0; j < fields.length; j++) {
            for (int i = 0; i < temp.getTotal(); i++) {
                if (temp.getField(i) == Mark.EMPTY) {
                    int[] areas = {
                        1,
                        temp.getDim() * 2,
                        (temp.getDim() * 2) - 1,
                        (temp.getDim() * 2) + 1
                    };
                    for (int area : areas) {
                        int count = 0;
                        while (temp.isField(i + area * (count + 1))) {
                            if (count == 5) {
                                break;
                            }
                            if (temp.getField(i + area * (count + 1)) == fields[j]) {
                                count++;
                            } else if (temp.getField(i + area * (count + 1))
                                    == (fields[j] == Mark.BLACK ? Mark.WHITE : Mark.BLACK)) {
                                count = 0;
                                break;
                            } else if (temp.getField(i + area * (count + 1)) == Mark.EMPTY) {
                                if (i + area * (count + 1) == 5
                                        || i + area * (count + 1) == 11
                                        || i + area * (count + 1) == 17
                                        || i + area * (count + 1) == 23
                                        || i + area * (count + 1) == 29
                                        || i + area * (count + 1) == 35) {
                                    count = 0;
                                    break;
                                }
                                count++;
                                if (temp.isField(i + area * (count + 1))
                                        && temp.getField(i + area * (count + 1)) == fields[j]) {
                                    count++;
                                }
                                break;
                            }
                        }
                        counts.add(new Integer[]{i, j, count});
                    }
                }
                temp = board.deepCopy();
            }
            temp = board.deepCopy();
        }
        Integer[] get = new Integer[]{-1, -1, -1};
        for (Integer[] count : counts) {
            if (count[2] > get[2]) {
                get = count;
            }
        }
        return get[2] == -1 || get[2] == 0 || get[2] == 1
                ? (int) (Math.random() * board.getTotal()) : get[0];
    }

    /**
     * Determines the rotation for the computer player based on the smart strategy
     * In this case, the smart strategy is checking for winning condition before returning
     * the rotation
     * @param board the game board
     * @param mark the mark of the computer player
     * @return the computer player's chosen field
     */
    /*@ requires board != null && mark == Mark.BLACK || mark == Mark.WHITE;
        ensures board.isRotation(\result);
    */
     /*@ pure @*/
    @Override
    public int determineRotation(Board board, Mark mark) {
        Board temp = board.deepCopy();
        for (int i = 0; i < 8; i++) {
            temp.rotatePart(i);
            if (temp.hasWinner()) {
                return i;
            }
            temp = board.deepCopy();
        }
        return (int) (Math.random() * 7);
    }
}
