package clientside.client;

import gamelogic.game.Game;
import java.io.PrintWriter;

/**
 * The interface that represents
 * a Client of the Pentago
 * game!
 */
public interface Client {

    /**
     * This method gives a boolean value depending on
     * whether the 2 players passed as the parameter can
     * get in a game or not!
     * @param player1 - The first player who is going to be in the game!
     * @param player2 - The second player of the game!
     * @return true if the players can get in a game and false if
     * an error happened.
     */
    boolean newGame(String player1, String player2);

    /**
     * This method is used to access
     * the PrintWriter object that is used in the game!
     * @return A printWriter object used in game.
     */
    PrintWriter getPwGame();

    /**
     * This method is used to access another
     * PrintWriter object that is used in the game!
     * @return A printWriter object used in game.
     */
    PrintWriter getPwGameNet();

    /**
     * This method is used to access the game object
     * used by a client when in a game of pentago!
     * @return The game object when a client
     * is in a game.
     */
    Game getGame();

    /**
     * This method is used to access the client's
     * name!
     * @return The string representing the client's name.
     */
    String getClientName();

    /**
     * This method is used to access the client's
     * username in the game!
     * @return The string representing the client's
     * username.
     */
    String getUsername();

    /**
     * This method is used to access the supported
     * extensions of the server the client is connected to!
     * @return The string[] representing all the extensions
     * the server supports
     */
    String[] getSupportedExtensions();

    /**
     * The method used to start the client thread. When this
     * method is called, a new thread of the client class
     * will be created
     */
    void start();
}
