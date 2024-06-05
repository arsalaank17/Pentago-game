package gamelogic.player;

import gamelogic.board.Board;
import gamelogic.exception.InvalidInputException;
import gamelogic.exception.InvalidMoveException;
import gamelogic.exception.InvalidRotationException;

import java.io.IOException;
import java.io.PrintWriter;
import java.io.Reader;

/**
 * Class for maintaining a human player in Pentago. Module 2 project
 * @author Kevin Schurman and Arsalaan Khan
 */
public class HumanPlayer extends Player {
    private final Reader reader;
    private PrintWriter pw;
    /**
     * Creates a new human player object.
     * @param name String of the human players name
     * @param reader Reader that will be used take the input from the user
     * @param mark Mark of the human players mark
     */
    /*@ requires name != null;
        requires reader != null;
        requires mark == Mark.WHITE || mark == Mark.BLACK;
    @*/
    public HumanPlayer(String name, Reader reader, Mark mark) {
        super(name, mark);
        this.reader = reader;
    }

    /**
     * Creates a new human player object.
     * @param name String of the human players name
     * @param reader Reader that will be used take the input from the user
     * @param mark Mark of the human players mark
     * @param pw Prints information for the player to read
     */
    /*@ requires name != null;
        requires reader != null;
        requires mark == Mark.WHITE || mark == Mark.BLACK;
        requires pw != null;
    @*/
    public HumanPlayer(String name, Reader reader, Mark mark, PrintWriter pw) {
        this(name, reader, mark);
        this.pw = pw;
    }

    /**
     * Asks the user to input the field where to place the next mark. This is
     * done using the standard input/output.
     * @param board the game board
     * @return the player's chosen field
     */
    /*@ requires board != null;
        ensures board.isField(\result) && board.getField(\result) == Mark.EMPTY;
    */
    /*@ pure */
    @Override
    public int determineMove(Board board) {
        boolean valid = false;
        int choice = -1;
        do {
            try {
                if (pw != null) {
                    pw.println("It's players turn - " + getName() + " :");
                    pw.println("ROW COL");
                }
                StringBuilder line = new StringBuilder();
                char c;
                while ((c = (char) reader.read()) != '\n') {
                    line.append(c);
                }
                String[] inputSplit = line.toString().split(" ");
                try {
                    if (inputSplit.length == 2) {
                        choice = board.index(Integer.parseInt(inputSplit[0].replaceAll(
                                "(\r)", "")),
                                Integer.parseInt(inputSplit[1].replaceAll("(\r)", "")));
                        valid = board.isField(choice) && board.isEmptyField(choice);
                    } else {
                        throw new InvalidInputException("Please make sure you are "
                                + "inputting the valid row AND the valid column! "
                                + "Input 2 integers, 1st one for the row and 2nd "
                                + "one for the column!");
                    }
                } catch (InvalidInputException e) {
                    System.out.println("Please make sure you are inputting the valid "
                            + "row AND the valid column! Input 2 integers, 1st one for "
                            + "the row and 2nd one for the column separated by a space! "
                            + "For example: 0 1\n");
                    System.out.println("Re-printing the board: Please input again!\n");
                    continue;
                }
                try {
                    if (!valid)  {
                        throw new InvalidMoveException("Please make sure you are inputting"
                                + "a valid move");
                    }
                } catch (InvalidMoveException e) {
                    System.out.println("Please make sure you are inputting a valid move.");
                    System.out.println("The field you are entering must be empty and the row "
                            + "and column should be a number from 0 to 5");
                    System.out.println("Re-printing the board now:");
                }
            } catch (IOException e) {
                System.out.println("ERROR: IO Exception. Please input correctly.");
            }
        } while (!valid);
        return choice;
    }

    /**
     * Asks the user to input the rotation number to rotate the board which is
     * done using the standard input/output.
     * @param board the game board
     * @return the player's chosen rotation
     */
    /*@ requires board != null;
        ensures board.isRotation(\result);
    @*/
    /*@ pure */
    @Override
    public int determineRotation(Board board) {
        boolean valid;
        int choice = -1;
        do {
            try {
                if (pw != null) {
                    pw.println("ROTATION");
                }
                StringBuilder line = new StringBuilder();
                char c;
                while ((c = (char) reader.read()) != '\n') {
                    line.append(c);
                }
                try {
                    choice = Integer.parseInt(String.valueOf(line).replaceAll("(\r)", ""));
                } catch (NumberFormatException e) {
                    System.out.println("Please only enter 1 integer!");
                }
                valid = board.isRotation(choice);
                try {
                    if (!valid) {
                        throw new InvalidRotationException("Please make sure you " +
                                "are inputting a valid rotation");
                    }
                } catch (InvalidRotationException e) {
                    System.out.println("Please make sure you are inputting a valid rotation!\n"
                            + "The rotation should be a number from 0 to 7"
                            + "Asking for rotation again now:");
                }
            } catch (IOException e) {
                System.out.println("Error! There was an IO exception!"
                        + "Please make sure you have input an integer as the rotation number!");
                valid = false;
            }
        } while (!valid);
        return choice;
    }
}
