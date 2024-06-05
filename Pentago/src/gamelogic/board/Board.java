package gamelogic.board;

import gamelogic.player.Mark;
/**
 * Board interface for the pentago game. Module 2 programming project
 * @author Kevin Schurman and Arsalaan Khan
 */
public interface Board {
    /**
     * Creates a deep copy of the board.
     * @return Board the deep copy of the Board
     */
    /*@ ensures \result != this;
        ensures (\forall int i; (i >= 0 && i < getTotal());
            \result.getField(i) == this.getField(i));
     */
    Board deepCopy();

    /**
     * Empties all fields of this board. Sets all the
     * fields on the board to be EMPTY
     */
    //@ ensures (\forall int i; (i >= 0 && i < getTotal()); getField(i) == Mark.EMPTY);
    void reset();

    /**
     * This method is used to return PARTS of the Board.
     * @return int the number of parts of the board
     */
    //@ requires true;
    /*@ pure */
    int getParts();

    /**
     * This method is used to return DIM
     * @return int the dimensions of each board
     */
    //@ requires true;
    /*@ pure */
    int getDim();

    /**
     * This method is used to return TOTAL
     * @return the total number of fields of the board
     */
    //@ requires true;
    /*@ pure */
    int getTotal();

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
    /*@ pure */
    int index(int row, int col);

    /**
     * Calculates the row and col from the index of the array.
     * @param index of the array
     * @return the array of the row and col
     */
    //@ requires isField(index);
    /*@ pure */
    Integer[] indexToRowCol(int index);

    /**
     * Returns true if index is a valid index of a field on the board.
     * @param index int of the index
     * @return true if index is greater or equals to 0 and index is smaller than TOTAL
     */
    //@ ensures index >= 0 && index < getTotal() ==> \result == true;
    /*@ pure */
    boolean isField(int index);

    /**
     * Returns the content of the field index.
     * @param index the index number of the field
     * @return the mark on the field
     */
    /*@ requires isField(index);
        ensures \result == Mark.EMPTY || \result == Mark.WHITE || \result == Mark.BLACK;
     */
    /*@ pure */
    Mark getField(int index);

    /**
     * Returns true if the field index is empty.
     * @param index the index of the field
     * @return true if the field is empty
     */
    /*@ requires isField(index);
        ensures getField(index) == Mark.EMPTY ==> \result == true;
     */
    /*@ pure */
    boolean isEmptyField(int index);

    /**
     * Sets the content of fields index to the mark.
     * @param index the field number
     * @param mark the mark to be placed
     */
    /*@ requires isField(index);
        ensures getField(index) == mark;
     */
    void setField(int index, Mark mark);

    /**
     * Returns true if the rotation specified is a valid rotation.
     * @param rotation the rotation number
     * @return true if the rotation is valid
     */
     //@ ensures rotation >= 0 && rotation <= 7 ==> \result == true;
    /*@ pure */
    boolean isRotation(int rotation);

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
    void rotatePart(int rotation);

    /**
     * Tests if the whole board is full.
     * @return true if all fields are occupied
     */
    /*@ ensures (\forall int i; (i >= 0 && i < getTotal());
        getField(i) == Mark.WHITE || getField(i) == Mark.BLACK);
    */
    /*@ pure */
    boolean isFull();

    /**
     * Returns true if the game is over. The game is over when there is a winner
     * or the whole board is full.
     * @return true if the game is over
     */
    //@ ensures isFull() && hasWinner() ==> \result == true;
    /*@ pure */
    boolean gameOver();

    /**
     * Returns true if the game has a winner. This is the case when one of the
     * marks controls at least one row, column or diagonal.
     * To control a row, column or diagonal the player must have 5 in a row in either of them.
     * @return true if the game has a winner
     */
    //@ ensures isWinner(Mark.WHITE) || isWinner(Mark.BLACK) ==> \result == true;
    /*@ pure */
    boolean hasWinner();

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
    boolean isWinner(Mark mark);

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
    boolean hasRow(Mark mark);

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
    boolean hasCol(Mark mark);

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
    boolean hasDiagonal(Mark mark);

    /**
     * Gives the user a hint of an empty field to use.
     * @return int index of the empty field
     */
    /*@ ensures isField(\result);
        ensures isEmptyField(\result);
    */
    /*@ pure */
    int getHint();
}
