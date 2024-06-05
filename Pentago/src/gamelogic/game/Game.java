package gamelogic.game;

import gamelogic.board.Board;
import gamelogic.player.Player;

/**
 * Interface for maintaining the Pentago game.
 * Module 2 Project 2022 University of Twente
 * @author Kevin Schurman and Arsalaan Khan
 */
public interface Game {
    /**
     * Starts the Pentago game.
     * Continues until either the board has a winner or the board is full
     */
    void startGame();

    /**
     * Prints the game situation.
     * @return String of the current updated board
     */
    //@ requires getBoard() != null;
    /*@ pure */
    String update();

    /**
     * Prints the result of the last game.
     * @return String of the result of the board
     */
    //@ requires getBoard().hasWinner() || getBoard().gameOver();
    /*@ pure */
    String result();

    /**
     * This method is used to return the Pentago Board object
     * @return Board of the current board
     */
    //@ requires true;
    /*@ pure */
    Board getBoard();

    /**
     * This method is used to return the players in the Pentago game
     * @return Player[] of the player arrays
     */
    //@ requires true;
    /*@ pure */
    Player[] getPlayers();

    /**
     * This method is used to return the Player object whose turn it is
     * in the Pentago game
     * @return Player of the currently playing player
     */
    //@ requires true;
    /*@ pure */
    Player getCurrent();

    /**
     * This method is used to return the amount of moves made
     * in the Pentago game
     * @return int of the amount of moves made in the game
     */
    //@ requires true;
    /*@ pure */
    int getMoves();
}
