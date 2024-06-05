package serverside.server;

import serverside.clienthandler.ClientHandler;
import serverside.gamehandler.GameHandler;

import java.util.List;

public interface Server {
    /**
     * This returns a String array with all the supported
     * extensions that the server is able to do when communicating with
     * the client.
     * @return supportedExtensions for the client to see what they cna do
     */
    String[] getSupportedExtensions();

    /**
     * The start method of the server which
     * starts the server on it's port which
     * would have been specified in this class's
     * constructor when creating a new ServerMethod
     * object.
     */
    void start();

    /**
     * Used to stop the server and close the
     * serverSocket. Also removes all the clients
     * connected to this server.
     */
    void stop();

    /**
     * Used to add a clientHandler object
     * to the server!
     * @param c - The clientHandler object to be
     *          added
     * @param number - An int to store the
     *               client's number which is
     *               used to identify a client
     *
     */
    void addClient(ClientHandler c, int number);

    /**
     * Used to remove a clientHandler object
     * to the server!
     * @param c - The clientHandler object
     *          to be removed
     *
     */
    void removeClient(ClientHandler c);

    /**
     * Used to access the list of clients
     * stored in the server.
     * @return a list of connected clients containing
     * clientHandler objects.
     */
    List<ClientHandler> getClientHandlers();

    /**
     * Used to return the gameHandler object
     * which handles a game of Pentago being
     * played on the server.
     * @return gameHandler
     */
    GameHandler getGameHandler();
}
