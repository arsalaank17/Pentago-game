package serverside.clienthandler;

import java.io.*;

/**
 * The client handler responsible for
 * handling the messages sent by the
 * client and sending messages to the client
 * when not in a game of Pentago but
 * connected to the Server. Whenever a client
 * connects to the server a new clientHandler
 * object is created for the client.
 * Once a game has started the GameHandler then
 * handles the messages until the game is over.
 * @author Kevin Schurman and Arsalaan Khan
 */
public interface ClientHandler {
    /**
     * The method is used to access the PipedReader
     * used by the clientHandler.
     * @return the PipedReader used by the clientHandler
     * to read incoming data from the client
     */
    PipedReader getGameIn();

    /**
     * The method is used to access the PrintWriter
     * used by the clientHandler.
     * @return the PrintWriter used by the clientHandler
     * to send data to the client.
     */
    PrintWriter getOut();

    /**
     * The method is used to access the client's client name.
     * @return the String which contains the client's
     * client name.
     */
    String getClientName();

    /**
     * The method is used to access the client's username.
     * @return the String which contains the client's
     * username.
     */
    String getUsername();

    /**
     * This method is used to send a message
     * to the client using the printWriter.
     * @param message the String to be sent to
     *                the client.
     */
    void sendToClient(String message);

    /**
     * This method is used to access the boolean
     * getInGame which indicates if a clientHandler
     * is in a game or not.
     * @return the true if the client is in a game
     * and false otherwise.
     */
    boolean getInGame();

    /**
     * This method is used to modify the inGame
     * boolean which indicates if a client is in the
     * game or not.
     * @param bool which is a boolean and can be either
     *             true or false depending on whether
     *             the client is in a game.
     */
    void setInGame(boolean bool);

    /**
     * This method used to exit and stop the client
     * handler. It closes all the readers and writers and
     * also closes the socket used by the client handler
     * to end the connection with the server.
     */
    void close();
}
