package serverside.server;

import serverside.clienthandler.ClientHandler;
import serverside.clienthandler.ClientHandlerMethod;
import serverside.gamehandler.GameHandler;
import serverside.gamehandler.GameHandlerMethod;

import java.io.IOException;
import java.net.ServerSocket;
import java.util.*;

/**
 * The server class for the Pentago game!
 * This class is responsible for the server that
 * will be started to host other clients to play the pentago
 * game!
 */
public class ServerMethod implements Server, Runnable {
    private final String[] supportedExtensions = new String[]{"RANK"};
    private Map<ClientHandler, Thread> handlers;
    private final List<ClientHandler> clients = new ArrayList<>();
    private GameHandler gameHandler;
    private final ServerSocket ss;
    private boolean running = true;

    /**
     * This is the constructor for the server
     * which creates a new server and has a port
     * it should start at as a parameter.
     * @param ss - server socket which is where the
     * server is housed in.
     */
    public ServerMethod(ServerSocket ss) {
        this.ss = ss;
    }

    /**
     * This returns a String array with all the supported
     * extensions that the server is able to do when communicating with
     * the client.
     * @return supportedExtensions for the client to see what they cna do
     */
    @Override
    public String[] getSupportedExtensions() {
        return supportedExtensions;
    }

    /**
     * The start method of the server which
     * starts the server on it's port which
     * would have been specified in this class's
     * constructor when creating a new ServerMethod
     * object.
     */
    @Override
    public void start() {
        handlers = new HashMap<>();
        gameHandler = new GameHandlerMethod();
        new Thread((Runnable) gameHandler).start();
        run();
    }

    /**
     * Used to stop the server and close the
     * serverSocket. Also removes all the clients
     * connected to this server.
     */
    @Override
    public void stop() {
        try {
            running = false;
            for (ClientHandler c : handlers.keySet()) {
                removeClient(c);
            }
            ss.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    /**
     * Used to create a new clientHandler object
     * everytime a client connects to the
     * server.
     */
    @Override
    public void run() {
        try {
            int number = 0;
            while (running) {
                addClient(new ClientHandlerMethod(ss.accept(), this), number++);
            }
        } catch (IOException e) {
            running = false;
        }
        stop();
    }

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
    @Override
    public void addClient(ClientHandler c, int number) {
        clients.add(c);
        handlers.put(c, new Thread((Runnable) c, "Client-Thread-" + number));
        handlers.get(c).start();
    }

    /**
     * Used to remove a clientHandler object
     * to the server!
     * @param c - The clientHandler object
     *          to be removed
     *
     */
    @Override
    public void removeClient(ClientHandler c) {
        if (clients.contains(c)) {
            System.out.println(
                    "Disconnected: [" + c.getClientName() + " | " + c.getUsername() + "]");
            clients.remove(c);
            handlers.remove(c);
            c.close();
        }
    }

    /**
     * Used to access the list of clients
     * stored in the server.
     * @return a list of connected clients containing
     * clientHandler objects.
     */
    @Override
    public List<ClientHandler> getClientHandlers() {
        return clients;
    }

    /**
     * Used to return the gameHandler object
     * which handles a game of Pentago being
     * played on the server.
     * @return gameHandler
     */
    @Override
    public GameHandler getGameHandler() {
        return gameHandler;
    }
}