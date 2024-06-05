package gamelogic.test;

import gamelogic.board.Board;
import gamelogic.player.Mark;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.BeforeEach;

import gamelogic.board.BoardMethod;

import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.*;

/**
 * The test class which contains the unit cases for the board method.
 * This is to see if the board class works
 * @author Kevin Schurman and Arsalaan Khan
 */
public class BoardMethodTest {
    private Board board;

    /**
     * The method which will be called before
     * executing any tests! This method creates a new
     * board
     */
    @BeforeEach
    public void setUp() {
        board = new BoardMethod();
    }

    /**
     * This method tests the initial setup of the board.
     * Tests if all the fields of the board are empty or not.
     * Test passes if they are empty.
     * Test fails if any of the fields are not empty
     */
    @Test
    public void testSetup() {
        for (int i = 0; i < board.getTotal(); i++) {
            assertEquals(Mark.EMPTY, board.getField(i));
        }
    }

    /**
     * This method tests the reset method of the Board class
     * The reset method sets all the fields of the board to be empty.
     * Test passes if the fields are empty after calling the reset method
     * Test fails if the fields are not empty.
     */
    @Test
    public void testReset() {
        board.setField(0, Mark.WHITE);
        board.setField(board.getTotal() - 1, Mark.BLACK);
        board.reset();
        assertEquals(Mark.EMPTY, board.getField(0));
        assertEquals(Mark.EMPTY, board.getField(board.getTotal() - 1));
    }

    /**
     * This method tests the deepCopy method of the Board class
     * The deepCopy method creates a new board with the same fields as the board
     * it deepCopied.
     * Test passes if the fields are the same as the board it deep-copied
     * Test fails if the fields are not the same
     */
    @Test
    public void testDeepCopy() {
        board.setField(0, Mark.WHITE);
        board.setField(board.getTotal() - 1, Mark.BLACK);
        Board deepCopyBoard = board.deepCopy();

        for (int i = 0; i < board.getTotal(); i++) {
            assertEquals(board.getField(i), deepCopyBoard.getField(i));
        }

        deepCopyBoard.setField(0, Mark.BLACK);
        assertEquals(Mark.WHITE, board.getField(0));
        assertEquals(Mark.BLACK, deepCopyBoard.getField(0));
    }

    /**
     * This test requires JUnit 5.8.1 and won't run in lower versions.
     * This method tests if the board that we have created
     * is indeed an instance of the Board class
     * Test passes if it is an instance of the Board class
     * Test fails if it is not an instance of the board class
     */
    @Test
    public void testInstanceOf() {
        assertInstanceOf(Board.class, board);
    }

    /**
     * This method tests the index(row, col) of the Board class.
     * The index method returns the index number of a particular combination of row
     * and column.
     * Test passes if the index is correct after giving particular rows and columns
     * as parameters.
     * Test fails if the index in incorrect after giving particular rows and columns
     * as parameters.
     */
    @Test
    public void testIndexArr() {
        int index = 0;
        for (int i = 0; i < board.getDim() * 2; i++) {
            for (int j = 0; j < board.getDim() * 2; j++) {
                assertEquals(index, board.index(i, j));
                index++;
            }
        }
    }

    /**
     * This method tests the index(row, col) of the Board class.
     * The index method returns the index number of a particular combination of row
     * and column.
     * Test passes if the index is correct after giving particular rows and columns
     * as parameters.
     * Test fails if the index in incorrect after giving particular rows and columns
     * as parameters.
     */
    @Test
    public void testIndexRowCol() {
        assertEquals(0, board.index(0, 0));
        assertEquals(board.getTotal() - 1,
                board.index((board.getDim() * 2) - 1, (board.getDim() * 2) - 1));
    }


    /**
     * This method tests the isField(int index) of the Board class.
     * The isField checks if the index is indeed a field on the board or not
     * Test passes if the isField returns true for valid indexes and false for invalid indexes
     * Test fails if the isField returns false for valid index or true for invalid indexes
     */
    @Test
    public void testIsFieldIndex() {
        assertFalse(board.isField(-1));
        assertTrue(board.isField(0));
        assertTrue(board.isField(board.getTotal() - 1));
        assertFalse(board.isField(board.getTotal()));
    }

    /**
     * This method tests the isField(int row, int col) of the Board class.
     * The isField checks if the row and column combination is indeed a field on the board or not
     * Test passes if the isField returns true for valid combinations of row and column
     * and false for invalid combinations.
     * Test fails if the isField returns false for valid combinations of row and column
     * or true for invalid combinations
     */
    @Test
    public void testIsFieldRowCol() {
        assertFalse(board.isField(board.index(-1, 0)));
        assertFalse(board.isField(board.index(0, -1)));
        assertTrue(board.isField(board.index(0, 0)));
        assertTrue(board.isField(board.index(2, 2)));
        assertTrue(board.isField(board.index(2, 3)));
        assertFalse(board.isField(board.index(6, 2)));
    }

    /**
     * This method tests the setField(int index) and getField(int index)
     * of the Board class. The set field sets the field to a MARK and
     * the getField returns the MARK of the field
     * The test passes if the getField indeed returns what has been set
     * by the setField
     * The test fails if the getField does not return what has been set
     * by the setField
     */
    @Test
    public void testSetAndGetFieldIndex() {
        board.setField(0, Mark.WHITE);
        assertEquals(Mark.WHITE, board.getField(0));
        assertEquals(Mark.EMPTY, board.getField(1));
    }

    /**
     * This method tests the setField and getField of the Board class but
     * giving rows and columns as parameters now instead
     * of indexes. The set field sets the field to a MARK and
     * the getField returns the MARK of the field
     * The test passes if the getField indeed returns what has been set
     * by the setField
     * The test fails if the getField does not return what has been set
     * by the setField
     */
    @Test
    public void testSetAndGetFieldRowCol() {
        board.setField(board.index(0, 0), Mark.WHITE);
        assertEquals(Mark.WHITE, board.getField(board.index(0, 0)));
        assertEquals(Mark.EMPTY, board.getField(board.index(0, 1)));
        assertEquals(Mark.EMPTY, board.getField(board.index(1, 0)));
        assertEquals(Mark.EMPTY, board.getField(board.index(1, 1)));
    }

    /**
     * This method tests the isEmptyField of the Board class with
     * index as its parameter which returns
     * a boolean indicating if the field is empty or not.
     * The test passes if the isEmptyField returns True on an empty field
     * and false on a field having MARK.WHITE or MARK.BLACK.
     * The test fails if the isEmptyField returns False on an empty field
     * or true on a non-empty field.
     */
    @Test
    public void testIsEmptyFieldIndex() {
        board.setField(0, Mark.WHITE);
        assertFalse(board.isEmptyField(0));
        assertTrue(board.isEmptyField(1));
    }

    /**
     * This method tests if the row and col data equals to the
     * index data provided.
     */
    @Test
    public void testRowAndColEqualsIndex() {
        Integer[] data = board.indexToRowCol(8);
        assertEquals(data[0], 1);
        assertEquals(data[1], 2);
    }

    /**
     * This method tests the isEmptyField of the Board class with
     * rows and columns as its parameter which returns
     * a boolean indicating if the field is empty or not.
     * The test passes if the isEmptyField returns True on an empty field
     * and false on a field having MARK.WHITE or MARK.BLACK.
     * The test fails if the isEmptyField returns False on an empty field
     * or true on a non-empty field.
     */
    @Test
    public void testIsEmptyFieldRowCol() {
        board.setField(board.index(0, 0), Mark.WHITE);
        assertFalse(board.isEmptyField(board.index(0, 0)));
        assertTrue(board.isEmptyField(board.index(0, 1)));
        assertTrue(board.isEmptyField(board.index(1, 0)));
    }

    /**
     * This method tests the hasRow method of the Board class with
     * which returns a boolean indicating if a mark controls any row on the
     * board or not. Controlling a row means having 5 of the same MARK in any of the rows
     * in a row(consecutively)
     * The test passes if the hasRow returns true when either of the marks control a row
     * and false when neither control the row
     * The test fails if the hasRow returns false when either of the marks control a row
     * or true when neither control the row
     */
    @Test
    public void testHasRow() {
        Mark[] mark = {Mark.BLACK, Mark.WHITE};
        for (int curr = 0; curr < mark.length; curr++) {
            for (int j = 0; j < board.getDim() * 2; j++) {
                for (int i = 0; i < board.getDim() * 2 - 1; i++) {
                    board.setField(board.index(j, i), mark[curr]);
                    if (i != 4) {
                        assertFalse(board.hasRow(mark[curr]));
                    } else {
                        assertTrue(board.hasRow(mark[curr]));
                        assertFalse(board.hasRow(mark[1 - curr]));
                    }
                }
                board.reset();
                for (int i = 1; i < board.getDim() * 2; i++) {
                    board.setField(board.index(j, i), mark[curr]);
                    if (i != 5) {
                        assertFalse(board.hasRow(mark[curr]));
                    } else {
                        assertTrue(board.hasRow(mark[curr]));
                        assertFalse(board.hasRow(mark[1 - curr]));
                    }
                }
                board.reset();
            }
            board.reset();
        }
    }

    /**
     * This method tests the hasRow method of the Board class with
     * which returns a boolean indicating if a mark controls any row on the
     * board or not. Controlling a column means having 5 of the same MARK in any of the columns
     * in a row(consecutively)
     * The test passes if the hasRow returns true when either of the marks control a column
     * and false when neither control the column
     * The test fails if the hasRow returns false when either of the marks control a column
     * or true when neither control the column
     */
    @Test
    public void testHasCol() {
        Mark[] mark = {Mark.BLACK, Mark.WHITE};
        for (int curr = 0; curr < mark.length; curr++) {
            for (int j = 0; j < board.getDim() * 2; j++) {
                for (int i = 0; i < board.getDim() * 2 - 1; i++) {
                    board.setField(board.index(i, j), mark[curr]);
                    if (i != 4) {
                        assertFalse(board.hasCol(mark[curr]));
                    } else {
                        assertTrue(board.hasCol(mark[curr]));
                        assertFalse(board.hasCol(mark[1 - curr]));
                    }
                }
                board.reset();
                for (int i = 1; i < board.getDim() * 2; i++) {
                    board.setField(board.index(i, j), mark[curr]);
                    if (i != 5) {
                        assertFalse(board.hasCol(mark[curr]));
                    } else {
                        assertTrue(board.hasCol(mark[curr]));
                        assertFalse(board.hasCol(mark[1 - curr]));
                    }
                }
                board.reset();
            }
            board.reset();
        }
    }

    @Test
    public void testIsFull() {
        IntStream.range(0, board.getTotal() - 1).forEach(i -> board.setField(i, Mark.WHITE));
        assertFalse(board.isFull());
        board.setField(board.getTotal() - 1, Mark.WHITE);
        assertTrue(board.isFull());
    }

    /**
     * This method tests the hasWinner method of the Board class which returns a boolean
     * indicating if a mark controls any row, column, or diagonal on the
     * board or not. Controlling a column, row or diagonal means having 5 of the same MARK
     * in a row in any of the column, row or diagonal respectively.
     * This specific tests if hasWinner is valid when a mark controls a diagonal or not.
     * The test passes if the hasWinner returns true when either of the marks control a
     * diagonal and false if they don't. The test fails if the hasWinner returns false
     * when either of the marks control a diagonal or true when neither control the diagonal
     */
    @Test
    public void testHasWinnerDiagonal() {
        for (int i = 0; i < 29; i += 7) {
            board.setField(i, Mark.WHITE);
            if (i != 28) {
                assertFalse(board.hasWinner());
            } else {
                assertTrue(board.hasWinner());
            }
        }

        board.reset();

        for (int i = 1; i < 30; i += 7) {
            board.setField(i, Mark.BLACK);
            if (i != 29) {
                assertFalse(board.hasWinner());
            } else {
                assertTrue(board.hasWinner());
            }
        }

        board.reset();

        for (int i = 4; i < 25; i += 5) {
            board.setField(i, Mark.BLACK);
            if (i != 24) {
                assertFalse(board.hasWinner());
            } else {
                assertTrue(board.hasWinner());
            }
        }

        board.reset();

        for (int i = 5; i < 26; i += 5) {
            board.setField(i, Mark.BLACK);
            if (i != 25) {
                assertFalse(board.hasWinner());
            } else {
                assertTrue(board.hasWinner());
            }
        }
        board.reset();

        for (int i = 6; i < 35; i += 7) {
            board.setField(i, Mark.BLACK);
            if (i != 34) {
                assertFalse(board.hasWinner());
            } else {
                assertTrue(board.hasWinner());
            }
        }
        board.reset();


        for (int i = 7; i < 36; i += 7) {
            board.setField(i, Mark.BLACK);
            if (i != 35) {
                assertFalse(board.hasWinner());
            } else {
                assertTrue(board.hasWinner());
            }
        }
        board.reset();

        for (int i = 10; i < 31; i += 5) {
            board.setField(i, Mark.BLACK);
            if (i != 30) {
                assertFalse(board.hasWinner());
            } else {
                assertTrue(board.hasWinner());
            }
        }
        board.reset();

        for (int i = 11; i < 32; i += 5) {
            board.setField(i, Mark.BLACK);
            if (i != 31) {
                assertFalse(board.hasWinner());
            } else {
                assertTrue(board.hasWinner());
            }
        }
        board.reset();
    }

    /**
     * This method tests the isWinner method of the Board class which returns a boolean
     * indicating if a particular mark controls any row, column, or diagonal on the
     * board or not. Controlling a column, row or diagonal means having 5 of the same MARK
     * in a row in any of the column, row or diagonal respectively. This test tests if
     * the correct mark is the winner if it controls a row , column or diagonal.
     * The test passes if isWinner returns true when the mark passed as the parameter controls
     * a row, column or diagonal and false when it doesn't. It should also return false
     * for the other mark which doesn't control anything.
     * The test fails if isWinner returns false when the mark passed as the parameter controls a
     * row, column or diagonal or true when it doesn't. It also fails if it returns true
     * for the other mark when it doesn't control anything.
     */
    @Test
    public void testIsWinner() {
        for (int i = 0; i < 29; i += 7) {
            board.setField(i, Mark.WHITE);
            if (i != 28) {
                assertFalse(board.isWinner(Mark.WHITE));
                assertFalse(board.isWinner(Mark.BLACK));
            } else {
                assertTrue(board.isWinner(Mark.WHITE));
                assertFalse(board.isWinner(Mark.BLACK));
            }
        }
        board.reset();

        for (int i = 6; i < 11; i++) {
            board.setField(i, Mark.BLACK);
            if (i != 10) {
                assertFalse(board.isWinner(Mark.WHITE));
                assertFalse(board.isWinner(Mark.BLACK));
            } else {
                assertTrue(board.isWinner(Mark.BLACK));
                assertFalse(board.isWinner(Mark.WHITE));
            }
        }
        board.reset();

        for (int i = 0; i < 25; i += 6) {
            board.setField(i, Mark.WHITE);
            if (i != 24) {
                assertFalse(board.isWinner(Mark.WHITE));
                assertFalse(board.isWinner(Mark.BLACK));
            } else {
                assertTrue(board.isWinner(Mark.WHITE));
                assertFalse(board.isWinner(Mark.BLACK));
            }
        }
    }


    @Test
    public void testHasNoWinnerGameOver() {
        for (int i = 0; i < board.getTotal(); i += 4) {
            board.setField(i, Mark.WHITE);
            board.setField(i + 1, Mark.WHITE);
            board.setField(i + 2, Mark.BLACK);
            board.setField(i + 3, Mark.BLACK);
        }
        assertFalse(board.hasWinner());
        assertTrue(board.gameOver());
    }

    /**
     * This method tests the hasWinner method of the Board class which returns a boolean
     * indicating if a mark controls any row, column, or diagonal on the
     * board or not. Controlling a column, row or diagonal means having 5 of the same MARK
     * in a row in any of the column, row or diagonal respectively.
     * This specific tests if hasWinner is accurate when a mark controls a row or not
     * The test passes if the hasWinner returns true when either of the
     * marks control a row and false if they don't. The test fails if the hasWinner returns false
     * when either of the marks control a row or true when neither control the row
     */
    @Test
    public void testHasWinnerRow() {
        Mark[] mark = {Mark.BLACK, Mark.WHITE };
        for (Mark value : mark) {
            for (int j = 0; j < board.getDim() * 2; j++) {
                for (int i = 0; i < board.getDim() * 2 - 1; i++) {
                    board.setField(board.index(j, i), value);
                    if (i != 4) {
                        assertFalse(board.hasWinner());
                    } else {
                        assertTrue(board.hasWinner());
                    }
                }
                board.reset();
                for (int i = 1; i < board.getDim() * 2; i++) {
                    board.setField(board.index(j, i), value);
                    if (i != 5) {
                        assertFalse(board.hasWinner());
                    } else {
                        assertTrue(board.hasWinner());
                    }
                }
                board.reset();
            }
            board.reset();
        }
    }

    /**
     * This method tests the hasWinner method of the Board class which returns a boolean
     * indicating if a mark controls any row, column, or diagonal on the
     * board or not. Controlling a column, row or diagonal means having 5 of the same MARK
     * in a row in any of the column, row or diagonal respectively. This specific tests
     * if hasWinner is accurate when a mark controls a column or not. The test passes
     * if the hasWinner returns true when either of the
     * marks control a column and false if they don't. The test fails if the hasWinner returns false
     * when either of the marks control a column or true when neither control the column
     */
    @Test
    public void testHasWinnerCol() {
        Mark[] mark = {Mark.BLACK, Mark.WHITE};
        for (Mark value : mark) {
            for (int j = 0; j < board.getDim() * 2; j++) {
                for (int i = 0; i < board.getDim() * 2 - 1; i++) {
                    board.setField(board.index(i, j), value);
                    if (i != 4) {
                        assertFalse(board.hasWinner());
                    } else {
                        assertTrue(board.hasWinner());
                        assertTrue(board.hasCol(value));
                    }
                }
                board.reset();
                for (int i = 1; i < board.getDim() * 2; i++) {
                    board.setField(board.index(i, j), value);
                    if (i != 5) {
                        assertFalse(board.hasWinner());
                    } else {
                        assertTrue(board.hasWinner());
                    }
                }
                board.reset();
            }
            board.reset();
        }
    }

    /**
     * This method tests the isRotation method of the Board class which returns a boolean
     * indicating if the int rotation passed as the parameter is valid or not. The rotation must be
     * an integer from 0 to 7.
     * The test passes if isRotation returns true for numbers from 0 to 7 and false otherwise.
     * The test fails if isRotation returns false for numbers from 0 to 7 or true for other numbers.
     */
    @Test
    public void testIsRotation() {
        for (int i = -1; i <= 8; i++) {
            if (i <= -1 || i >= 8) {
                assertFalse(board.isRotation(i));
            } else {
                assertTrue(board.isRotation(i));
            }
        }
    }

    /**
     * This method tests the rotatePart method of the Board class which rotates the board.
     * This particular test tests the rotation with int 0 as the parameter which rotate the
     * top left subBoard counter-clockwise.
     * The test passes if the rotation is correct and the fields of the board
     * are shifted accordingly.
     * The test fails if the rotation is incorrect and the fields of the board
     * are not shifted appropriately.
     */
    @Test
    public void testRotationTopLeftCounterClockwise() {
        for (int i = 0; i <= 14; i += 6) {
            board.setField(i, Mark.WHITE);
            board.setField(i + 1, Mark.BLACK);
            board.setField(i + 2, Mark.BLACK);
        }
        board.rotatePart(0);
        for (int i = 12; i <= 14; i++) {
            assertEquals(board.getField(i), Mark.WHITE);
        }
        for (int i = 0; i <= 8; i += 6) {
            for (int j = 0; j < board.getDim(); j++) {
                assertEquals(board.getField(j), Mark.BLACK);
            }
        }
    }

    /**
     * This method tests the rotatePart method of the Board class which rotates the board.
     * This particular test tests the rotation with int 1 as the parameter which rotate the
     * top left subBoard clockwise.
     * The test passes if the rotation is correct and the fields of the board
     * are shifted accordingly.
     * The test fails if the rotation is incorrect and the fields of the board
     * are not shifted appropriately.
     */
    @Test
    public void testRotationTopLeftClockwise() {
        for (int i = 0; i <= 14; i += 6) {
            board.setField(i, Mark.WHITE);
            board.setField(i + 1, Mark.BLACK);
            board.setField(i + 2, Mark.BLACK);
        }
        board.rotatePart(1);
        for (int i = 0; i <= 2; i++) {
            assertEquals(board.getField(i), Mark.WHITE);
        }
        for (int i = 6; i <= 14; i += 6) {
            for (int j = 0; j < board.getDim(); j++) {
                assertEquals(board.getField(i + j), Mark.BLACK);
            }
        }
    }

    /**
     * This method tests the rotatePart method of the Board class which rotates the board.
     * This particular test tests the rotation with int 2 as the parameter which rotate the
     * top right subBoard counter-clockwise.
     * The test passes if the rotation is correct and the fields of the board
     * are shifted accordingly
     * The test fails if the rotation is incorrect and the fields of the board
     * are not shifted appropriately
     */
    @Test
    public void testRotationTopRightCounterClockwise() {
        for (int i = 3; i <= 17; i += 6) {
            board.setField(i, Mark.WHITE);
            board.setField(i + 1, Mark.BLACK);
            board.setField(i + 2, Mark.BLACK);
        }
        board.rotatePart(2);
        for (int i = 15; i <= 17; i++) {
            assertEquals(board.getField(i), Mark.WHITE);
        }
        for (int i = 3; i <= 11; i += 6) {
            for (int j = 0; j < board.getDim(); j++) {
                assertEquals(board.getField(i + j), Mark.BLACK);
            }
        }
    }

    /**
     * This method tests the rotatePart method of the Board class which rotates the board.
     * This particular test tests the rotation with int 3 as the parameter which rotate the
     * top right subBoard clockwise.
     * The test passes if the rotation is correct and the fields of the board
     * are shifted accordingly
     * The test fails if the rotation is incorrect and the fields of the board
     * are not shifted appropriately
     */
    @Test
    public void testRotationTopRightClockwise() {
        for (int i = 3; i <= 17; i += 6) {
            board.setField(i, Mark.WHITE);
            board.setField(i + 1, Mark.BLACK);
            board.setField(i + 2, Mark.BLACK);
        }
        board.rotatePart(3);
        for (int i = 3; i <= 5; i++) {
            assertEquals(board.getField(i), Mark.WHITE);
        }
        for (int i = 9; i <= 17; i += 6) {
            for (int j = 0; j < board.getDim(); j++) {
                assertEquals(board.getField(i + j), Mark.BLACK);
            }
        }
    }

    /**
     * This method tests the rotatePart method of the Board class which rotates the board.
     * This particular test tests the rotation with int 4 as the parameter which rotate the
     * bottom left subBoard counter-clockwise.
     * The test passes if the rotation is correct and the fields of the board
     * are shifted accordingly.
     * The test fails if the rotation is incorrect and the fields of the board
     * are not shifted appropriately.
     */
    @Test
    public void testRotationBottomLeftCounterClockwise() {
        for (int i = 18; i <= 32; i += 6) {
            board.setField(i, Mark.WHITE);
            board.setField(i + 1, Mark.BLACK);
            board.setField(i + 2, Mark.BLACK);
        }
        board.rotatePart(4);
        for (int i = 30; i <= 32; i++) {
            assertEquals(board.getField(i), Mark.WHITE);
        }
        for (int i = 18; i <= 26; i += 6) {
            for (int j = 0; j < board.getDim(); j++) {
                assertEquals(board.getField(i + j), Mark.BLACK);
            }
        }
    }

    /**
     * This method tests the rotatePart method of the Board class which rotates the board.
     * This particular test tests the rotation with int 5 as the parameter which rotate the
     * bottom left subBoard clockwise.
     * The test passes if the rotation is correct and the fields of the board
     * are shifted accordingly.
     * The test fails if the rotation is incorrect and the fields of the board
     * are not shifted appropriately.
     */
    @Test
    public void testRotationBottomLeftClockwise() {
        for (int i = 18; i <= 32; i += 6) {
            board.setField(i, Mark.WHITE);
            board.setField(i + 1, Mark.BLACK);
            board.setField(i + 2, Mark.BLACK);
        }
        board.rotatePart(5);
        for (int i = 18; i <= 20; i++) {
            assertEquals(board.getField(i), Mark.WHITE);
        }
        for (int i = 24; i <= 32; i += 6) {
            for (int j = 0; j < board.getDim(); j++) {
                assertEquals(board.getField(i + j), Mark.BLACK);
            }
        }
    }

    /**
     * This method tests the rotatePart method of the Board class which rotates the board.
     * This particular test tests the rotation with int 6 as the parameter which rotate the
     * bottom right subBoard counter-clockwise.
     * The test passes if the rotation is correct and the fields of the board
     * are shifted accordingly.
     * The test fails if the rotation is incorrect and the fields of the board
     * are not shifted appropriately.
     */
    @Test
    public void testRotationBottomRightCounterClockwise() {
        for (int i = 21; i <= 35; i += 6) {
            board.setField(i, Mark.WHITE);
            board.setField(i + 1, Mark.BLACK);
            board.setField(i + 2, Mark.BLACK);
        }
        board.rotatePart(6);
        for (int i = 33; i <= 35; i++) {
            assertEquals(board.getField(i), Mark.WHITE);
        }
        for (int i = 21; i <= 29; i += 6) {
            for (int j = 0; j < board.getDim(); j++) {
                assertEquals(board.getField(i + j), Mark.BLACK);
            }
        }
    }

    /**
     * This method tests the rotatePart method of the Board class which rotates the board.
     * This particular test tests the rotation with int 7 as the parameter which rotate the
     * bottom right subBoard clockwise.
     * The test passes if the rotation is correct and the fields of the board
     * are shifted accordingly.
     * The test fails if the rotation is incorrect and the fields of the board
     * are not shifted appropriately.
     */
    @Test
    public void testRotationBottomRightClockwise() {
        for (int i = 21; i <= 35; i += 6) {
            board.setField(i, Mark.WHITE);
            board.setField(i + 1, Mark.BLACK);
            board.setField(i + 2, Mark.BLACK);
        }
        board.rotatePart(7);
        for (int i = 21; i <= 23; i++) {
            assertEquals(board.getField(i), Mark.WHITE);
        }
        for (int i = 27; i <= 35; i += 6) {
            for (int j = 0; j < board.getDim(); j++) {
                assertEquals(board.getField(i + j), Mark.BLACK);
            }
        }
    }
}
