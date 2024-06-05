package gamelogic.board;

import gamelogic.player.Mark;

import java.util.Arrays;
import java.util.stream.IntStream;

/**
 * Board for the pentago game. Module 2 programming project
 * @author Kevin Schurman and Arsalaan Khan
 */
public class BoardMethod implements Board {
    private final Mark[] fields;
    private static final int PARTS = 4;
    private static final int DIM = 3;
    private static final int TOTAL = PARTS * DIM * DIM;

    /*@ private invariant fields.length == DIM * DIM  * PARTS;
        private invariant (\forall int i; (i >= 0 && i < 36);
            fields[i] == Mark.EMPTY || fields[i] == Mark.WHITE || fields[i] == Mark.BLACK);
        public invariant getParts() == 4;
        public invariant getDim() == 3;
        public invariant getTotal() == 36;
    @*/

    /**
     * Creates an empty board.
     */
    //@ ensures (\forall int i; (i >= 0 && i < TOTAL); fields[i] == Mark.EMPTY);
    public BoardMethod() {
        fields = new Mark[TOTAL];
        reset();
    }

    /**
     * Creates a deep copy of the board.
     * @return Board the deep copy of the Board
     */
    /*@ ensures \result != this;
        ensures (\forall int i; (i >= 0 && i < getTotal());
            \result.getField(i) == this.getField(i));
     */
    @Override
    public Board deepCopy() {
        Board board = new BoardMethod();
        for (int i = 0; i < TOTAL; i++) {
            board.setField(i, getField(i));
        }
        return board;
    }

    /**
     * Empties all fields of this board. Sets all the
     * fields on the board to be EMPTY
     */
    //@ ensures (\forall int i; (i >= 0 && i < getTotal()); getField(i) == Mark.EMPTY);
    @Override
    public void reset() {
        for (int i = 0; i < TOTAL; i++) {
            setField(i, Mark.EMPTY);
        }
    }

    /**
     * This method is used to return PARTS of the Board.
     * @return int the number of parts of the board
     */
    //@ requires true;
    /*@ pure */
    @Override
    public int getParts() {
        return PARTS;
    }

    /**
     * This method is used to return DIM
     * @return int the dimensions of each board
     */
    //@ requires true;
    /*@ pure */
    @Override
    public int getDim() {
        return DIM;
    }

    /**
     * This method is used to return TOTAL
     * @return the total number of fields of the board
     */
    //@ requires true;
    /*@ pure */
    @Override
    public int getTotal() {
        return TOTAL;
    }

    /**
     * Calculates the index in the linear array of fields from a (row, col)
     * pair.
     * @param row int of the row
     * @param col int of the column
     * @return the index belonging to the (row,col)-field
     */
    /*@ requires row >= 0 && row < 6;
        requires col >= 0 && col < 6;
     */
    @Override
    public int index(int row, int col) {
        return row >= 0 && row < (DIM * 2)
                && col >= 0 && col < (DIM * 2) ? DIM * (PARTS / 2) * row + col : -1;
    }

    /**
     * Calculates the row and col from the index of the array.
     * @param index of the array
     * @return the array of the row and col
     */
    //@ requires isField(index);
    /*@ pure */
    @Override
    public Integer[] indexToRowCol(int index) {
        Integer[] data = new Integer[2];
        int row = index / (DIM * 2);
        int col = index % (DIM * 2);
        if (isField(index) && isField(index(row, col)) && index == index(row, col)) {
            data[0] = row;
            data[1] = col;
        }
        return data;
    }

    /**
     * Returns true if index is a valid index of a field on the board.
     * @param index int of the index
     * @return true if index is greater or equals to 0 and index is smaller than TOTAL
     */
    //@ ensures index >= 0 && index < getTotal() ==> \result == true;
    /*@ pure */
    @Override
    public boolean isField(int index) {
        return index >= 0 && index < TOTAL;
    }

    /**
     * Returns the content of the field index.
     * @param index the index number of the field
     * @return the mark on the field
     */
    /*@ requires isField(index);
        ensures \result == Mark.EMPTY || \result == Mark.WHITE || \result == Mark.BLACK;
     */
    /*@ pure */
    @Override
    public Mark getField(int index) {
        return fields[index];
    }

    /**
     * Returns true if the field index is empty.
     * @param index the index of the field
     * @return true if the field is empty
     */
    /*@ requires isField(index);
        ensures getField(index) == Mark.EMPTY ==> \result == true;
     */
    /*@ pure */
    @Override
    public boolean isEmptyField(int index) {
        return getField(index) == Mark.EMPTY;
    }

    /**
     * Sets the content of fields index to the mark.
     * @param index the field number
     * @param mark the mark to be placed
     */
    /*@ requires isField(index);
        ensures getField(index) == mark;
     */
    @Override
    public void setField(int index, Mark mark) {
        fields[index] = mark;
    }

    /**
     * Returns true if the rotation specified is a valid rotation.
     * @param rotation the rotation number
     * @return true if the rotation is valid
     */
    //@ ensures rotation >= 0 && rotation <= 7 ==> \result == true;
    /*@ pure */
    @Override
    public boolean isRotation(int rotation) {
        return rotation >= 0 && rotation <= 7;
    }

    /**
     * Used to rotate a particular sub-board of the board.
     * rotation = 0 is rotating the top left sub-board counter-clockwise
     * rotation = 1 is rotating the top left sub-board clockwise
     * rotation = 2 is rotating the top right sub-board counter-clockwise
     * rotation = 3 is rotating the top right sub-board clockwise
     * rotation = 4 is rotating the bottom left sub-board counter-clockwise
     * rotation = 5 is rotating the bottom left sub-board clockwise
     * rotation = 6 is rotating the bottom right sub-board counter-clockwise
     * rotation = 7 is rotating the bottom right sub-board clockwise
     * @param rotation the rotation number
     */
    //@ requires isRotation(rotation);
    @Override
    public void rotatePart(int rotation) {
        Mark temp;
        switch (rotation) {
            case 0:
                temp = fields[0];
                fields[0] = fields[2];
                fields[2] = fields[14];
                fields[14] = fields[12];
                fields[12] = temp;
                temp = fields[1];
                fields[1] = fields[8];
                fields[8] = fields[13];
                fields[13] = fields[6];
                fields[6] = temp;
                break;
            case 1:
                temp = fields[0];
                fields[0] = fields[12];
                fields[12] = fields[14];
                fields[14] = fields[2];
                fields[2] = temp;
                temp = fields[1];
                fields[1] = fields[6];
                fields[6] = fields[13];
                fields[13] = fields[8];
                fields[8] = temp;
                break;
            case 2:
                temp = fields[3];
                fields[3] = fields[5];
                fields[5] = fields[17];
                fields[17] = fields[15];
                fields[15] = temp;
                temp = fields[4];
                fields[4] = fields[11];
                fields[11] = fields[16];
                fields[16] = fields[9];
                fields[9] = temp;
                break;
            case 3:
                temp = fields[3];
                fields[3] = fields[15];
                fields[15] = fields[17];
                fields[17] = fields[5];
                fields[5] = temp;
                temp = fields[4];
                fields[4] = fields[9];
                fields[9] = fields[16];
                fields[16] = fields[11];
                fields[11] = temp;
                break;
            case 4:
                temp = fields[18];
                fields[18] = fields[20];
                fields[20] = fields[32];
                fields[32] = fields[30];
                fields[30] = temp;
                temp = fields[19];
                fields[19] = fields[26];
                fields[26] = fields[31];
                fields[31] = fields[24];
                fields[24] = temp;
                break;
            case 5:
                temp = fields[18];
                fields[18] = fields[30];
                fields[30] = fields[32];
                fields[32] = fields[20];
                fields[20] = temp;
                temp = fields[19];
                fields[19] = fields[24];
                fields[24] = fields[31];
                fields[31] = fields[26];
                fields[26] = temp;
                break;
            case 6:
                temp = fields[21];
                fields[21] = fields[23];
                fields[23] = fields[35];
                fields[35] = fields[33];
                fields[33] = temp;
                temp = fields[22];
                fields[22] = fields[29];
                fields[29] = fields[34];
                fields[34] = fields[27];
                fields[27] = temp;
                break;
            case 7:
                temp = fields[21];
                fields[21] = fields[33];
                fields[33] = fields[35];
                fields[35] = fields[23];
                fields[23] = temp;
                temp = fields[22];
                fields[22] = fields[27];
                fields[27] = fields[34];
                fields[34] = fields[29];
                fields[29] = temp;
                break;
        }
    }

    /**
     * Tests if the whole board is full.
     * @return true if all fields are occupied
     */
    /*@ ensures (\forall int i; (i >= 0 && i < getTotal());
        getField(i) == Mark.WHITE || getField(i) == Mark.BLACK);
    */
    /*@ pure */
    @Override
    public boolean isFull() {
        return IntStream.range(0, TOTAL).noneMatch(this::isEmptyField);
    }

    /**
     * Returns true if the game is over. The game is over when there is a winner
     * or the whole board is full.
     * @return true if the game is over
     */
    //@ ensures isFull() && hasWinner() ==> \result == true;
    /*@ pure */
    @Override
    public boolean gameOver() {
        return isFull() || hasWinner();
    }

    /**
     * Returns true if the game has a winner. This is the case when one of the
     * marks controls at least one row, column or diagonal.
     * To control a row, column or diagonal the player must have 5 in a row in either of them.
     * @return true if the game has a winner
     */
    //@ ensures isWinner(Mark.WHITE) || isWinner(Mark.BLACK) ==> \result == true;
    /*@ pure */
    @Override
    public boolean hasWinner() {
        return (hasRow(Mark.BLACK) || hasCol(Mark.BLACK) || hasDiagonal(Mark.BLACK)) ||
               (hasRow(Mark.WHITE) || hasCol(Mark.WHITE) || hasDiagonal(Mark.WHITE));
    }

    /**
     * Checks if the mark has won. A mark wins if it controls at
     * least one row, column or diagonal.
     * @param mark the mark of interest
     * @return true if the mark has won
     */
    /*@ requires mark == Mark.WHITE || mark == Mark.BLACK;
        ensures hasRow(mark) || hasCol(mark) || hasDiagonal(mark) ==> \result == true;
     */
    /*@ pure */
    @Override
    public boolean isWinner(Mark mark) {
        return hasWinner() && (hasRow(mark) || hasCol(mark) || hasDiagonal(mark));
    }

    /**
     * Checks whether there is a row on the board which
     * have 5 of the same mark in a row in the row.
     * @param mark the Mark of interest
     * @return true if there is a row controlled by mark
     */
    /*@ requires mark == Mark.WHITE || mark == Mark.BLACK;
        ensures isWinner(mark);
        ensures hasWinner();
    */
    /*@ pure */
    @Override
    public boolean hasRow(Mark mark) {
        /*
          Using lambda expressions, we go through the range from 0 to DIM * 2, so we can check
          each row of the board. We use another range from 0 to 2 because we need since the board
          can be filled up to DIM * 2 - 1, we will also check if the board has been filled by the
          extra line with the offset included. We then check the range yet again from the current
          offset to (DIM * 2) - (1 - the offset) for the offset lines as well. We will need to
          check every single one of these array lines to see if it matches the mark.
          One last lambda expression is used to check if all the fields in the range gives us the
          mark. If it does so, it returns because of how we use the anyMatch() function on all the
          other ranges whereas the last one is to check if all the rows have been
          filled using the allMatch() function.
         */
        return IntStream.range(0, DIM * 2)
                .anyMatch(j -> IntStream.range(0, 2)
                        .anyMatch(x -> IntStream.range(x, (DIM * 2) - (1 - x))
                                .allMatch(i -> getField(index(j, i)) == mark)));
    }

    /**
     * Checks whether there is a column on the board
     * which have 5 of the same mark in a row in the column
     * @param mark the Mark of interest
     * @return true if there is a column controlled by mark
     */
    /*@ requires mark == Mark.WHITE || mark == Mark.BLACK;
        ensures isWinner(mark);
        ensures hasWinner();
    */
    /*@ pure */
    @Override
    public boolean hasCol(Mark mark) {
        /*
          Using lambda expressions, we go through the range from 0 to DIM * 2, so we can check each
          column of the board. We use another range from 0 to 2 because we need since the board can
          be filled up to DIM * 2 - 1, we will also check if the board has been filled by the extra
          line with the offset included. We then check the range yet again from the current offset
          to (DIM * 2) - (1 - the offset) for the offset lines as well. We will need to check every
          single one of these array lines to see if it matches the mark. One last lambda expression
          is used to check if all the fields in the range gives us the mark.
          If it does so, it returns because of how we use the anyMatch() function on all the other
          ranges whereas the last one is to check if all the columns have been filled using
          the allMatch() function.
         */
        return IntStream.range(0, DIM * 2)
                .anyMatch(j -> IntStream.range(0, 2)
                        .anyMatch(x -> IntStream.range(x, (DIM * 2) - (1 - x))
                                .allMatch(i -> getField(index(i, j)) == mark)));
    }

    /**
     * Checks whether there is a diagonal on the board
     * which have 5 of the same mark in a row in the diagonal
     * @param mark the Mark of interest
     * @return true if there is a diagonal controlled by mark
     */
    /*@ requires mark == Mark.WHITE || mark == Mark.BLACK;
        ensures isWinner(mark);
        ensures hasWinner();
    */
    /*@ pure */
    @Override
    public boolean hasDiagonal(Mark mark) {
        /*
          The data multidimensional array is being used as a means of instructions
          for the parts of the board that should have the correct conditions to verify
          that the board is completed. Assume x targets any one of these array, data[x][0]
          is the start range() whereas data[x][1] is the end range. This is for going
          through the whole board array, then using filter() to skip over all the unnecessary
          data checks with n being the number from the range, data[x][2] being the offset of
          the array, and data[x][3] being the modulo to see if this is the array we want to target.
          If the operation gives us 0, we check if all instances from the array gives us the mark.
          If it does so, the diagonal line is filled with the mark.
         */
        Integer[][] data = {
                {0, 29, 0, 7},
                {1, 30, 6, 7},
                {4, 25, 1, 5},
                {5, 26, 0, 5},
                {6, 35, 1, 7},
                {7, 36, 0, 7},
                {10, 31, 0, 5},
                {11, 32, 4, 5}
        };
        return Arrays.stream(data)
                .anyMatch(x -> IntStream.range(x[0], x[1])
                        .filter(n -> (n + x[2]) % x[3] == 0)
                        .allMatch(i -> getField(i) == mark));
    }

    /**
     * Gives the user a hint of an empty field to use.
     * @return int index of the empty field
     */
    /*@ ensures isField(\result);
        ensures isEmptyField(\result);
    */
    /*@ pure */
    @Override
    public int getHint() {
        int data;
        do {
            data = (int) (Math.random() * TOTAL);
        } while (!isEmptyField(data));
        return data;
    }

    /**
     * Returns a String representation of this board.
     * @return the game situation as String
     */
    //@ ensures \result != null;
    /*@ pure */
    @Override
    public String toString() {
        StringBuilder str = new StringBuilder("     ");
        for (int i = 0; i < getDim() * 2; i++) {
            str.append("COL").append(i).append("  ");
        }
        str.append("\n");
        for (int i = 0, j = 0; i < getTotal(); i++) {
            if (i % (getDim() * 2) == 0) {
                str.append("ROW").append(j++).append(" ");
            }
            switch (getField(i)) {
                case WHITE:
                    str.append((char) 27 + "[30;47;1m W ");
                    break;
                case BLACK:
                    str.append((char) 27 + "[37;40;1m B ");
                    break;
                default:
                    str.append("   ");
                    break;
            }
            str.append((char) 27 + "[0m");
            if (((i + 1) % (getDim() * 2)) != 0) {
                if ((i + 1) % getDim() != 0) {
                    str.append(" | ");
                } else {
                    str.append(" || ");
                }
            } else {
                if ((i + 1) != getTotal()) {
                    if ((i + 1) % (getDim() * 2 * getDim()) != 0) {
                        str.append("\n").append("     ").append("-----".repeat((getDim() * 2) + 1));
                    } else {
                        str.append("\n").append("     ").append("=====".repeat((getDim() * 2) + 1));
                    }
                }
                str.append("\n");
            }
        }
        return str.toString();
    }
}