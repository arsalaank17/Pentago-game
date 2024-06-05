package serverside.clienthandler;

import commands.ServerCommands;
import serverside.server.Server;

import java.io.*;
import java.net.Socket;
import java.util.*;

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
public class ClientHandlerMethod implements ClientHandler, Runnable {
    private final Socket s;
    private final Server gs;

    private final BufferedReader in;
    private final PipedReader ppr;
    private final PipedWriter ppw;
    private final PrintWriter pw;
    private final PrintWriter out;

    private final PipedReader pprGame;
    private final PrintWriter pwGame;

    private boolean running = false;
    private boolean pinging = false;
    private boolean inGame = false;
    private boolean initHello = false;
    private String clientName = null;
    private boolean initLogin = false;
    private String username = null;

    /**
     * The constructor for the client handler which
     * creates a new clientHandler object with the
     * passed parameters.
     * @param s - The socket used to connect to
     *          a server
     * @param gs - The game server it is going to connect to
     * @throws IOException  if the inputStreamReader cannot read
     * in case connection with the server cannot
     * be established
     */
    public ClientHandlerMethod(Socket s, Server gs) throws IOException {
        this.s = s;
        this.gs = gs;
        in = new BufferedReader(new InputStreamReader(s.getInputStream()));
        ppr = new PipedReader();
        ppw = new PipedWriter(ppr);
        pw = new PrintWriter(ppw, true);
        out = new PrintWriter(s.getOutputStream(), true);

        pprGame = new PipedReader();
        PipedWriter ppwGame = new PipedWriter(pprGame);
        pwGame = new PrintWriter(ppwGame, true);

    }

    /**
     * The method is used to access the PipedReader
     * used by the clientHandler.
     * @return the PipedReader used by the clientHandler
     * to read incoming data from the client
     */
    @Override
    public PipedReader getGameIn() {
        return pprGame;
    }

    /**
     * The method is used to access the PrintWriter
     * used by the clientHandler.
     * @return the PrintWriter used by the clientHandler
     * to send data to the client.
     */
    @Override
    public PrintWriter getOut() {
        return out;
    }

    /**
     * The method is used to access the client's client name.
     * @return the String which contains the client's
     * client name.
     */
    @Override
    public String getClientName() {
        return clientName;
    }

    /**
     * The method is used to access the client's username.
     * @return the String which contains the client's
     * username.
     */
    @Override
    public String getUsername() {
        return username;
    }

    /**
     * This method is used to send a message
     * to the client using the printWriter.
     * @param message the String to be sent to
     *                the client.
     */
    @Override
    public void sendToClient(String message) {
        out.println(message);
    }

    /**
     * This method is used to access the boolean
     * getInGame which indicates if a clientHandler
     * is in a game or not.
     * @return the true if the client is in a game
     * and false otherwise.
     */
    @Override
    public boolean getInGame() {
        return inGame;
    }

    /**
     * This method is used to modify the inGame
     * boolean which indicates if a client is in the
     * game or not.
     * @param bool which is a boolean and can be either
     *             true or false depending on whether
     *             the client is in a game.
     */
    @Override
    public void setInGame(boolean bool) {
        inGame = bool;
    }

    /**
     * This method used to exit and stop the client
     * handler. It closes all the readers and writers and
     * also closes the socket used by the client handler
     * to end the connection with the server.
     */
    @Override
    public void close() {
        try {
            running = false;
            in.close();
            pw.close();
            ppw.close();
            ppr.close();
            out.close();
            s.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    /**
     * The clientHandler class is a runnable
     * class and whenever a new thread of the ClientHandler
     * class is started , the code below is executed by a thread.
     * This code processes the incoming data from the client and
     * sends the data from the server to the client as well
     * depending on the message received by the client.
     */
    @Override
    public void run() {
        try {
            Thread thread;
            Thread pingThread = null;
            if (!running) {
                running = true;
                thread = new Thread(this, "ClientHandler-Running-Thread");
                thread.start();
                String str;
                while ((str = in.readLine()) != null) {
                    pw.println(str);
                }
                if (inGame) {
                    pwGame.println("");
                }
                assert false;
                if (pingThread.isAlive()) {
                    pingThread.interrupt();
                }
                thread.interrupt();
            } else if (pinging) {
                while (pinging) {
                    Thread.sleep(10000);
                    pinging = false;
                    sendToClient(ServerCommands.sPING());
                    Thread.sleep(10000);
                }
            } else {
                while (running) {
                    StringBuilder stringBuilder = new StringBuilder();
                    char c;
                    while ((c = (char) ppr.read()) != '\n') {
                        if (c != '\r') {
                            stringBuilder.append(c);
                        }
                    }
                    String[] message = stringBuilder.toString().split("~");
                    System.out.println(
                            "[" + clientName + " | " + username + "] - [" + stringBuilder + "]");
                    switch (message[0].toUpperCase()) {
                        // TODO BONUS: Auth, Chat, Crypt abilities
                        case "HELLO":
                            if (!initHello) {
                                if (message.length >= 2 && message[1] != null) {
                                    initHello = true;
                                    clientName = message[1];
                                    sendToClient(ServerCommands.sHELLO(
                                            "Arsalaan and Kevin's Server", gs.getSupportedExtensions()));
                                } else {
                                    sendToClient(ServerCommands.sERROR(
                                            "HELLO protocol gave incorrect arguments"));
                                }
                            } else {
                                sendToClient(ServerCommands.sERROR(
                                        "HELLO protocol handshake already initialized"));
                            }
                            break;
                        case "LOGIN":
                            if (initHello) {
                                if (message.length == 2) {
                                    boolean found = false;
                                    for (ClientHandler ch : gs.getClientHandlers()) {
                                        if (ch.getUsername() != null
                                                && ch.getUsername().equals(message[1])) {
                                            found = true;
                                            break;
                                        }
                                    }
                                    if (found) {
                                        sendToClient(ServerCommands.sALREADYLOGGEDIN());
                                    } else {
                                        initLogin = true;
                                        pinging = true;
                                        pingThread = new Thread(this,
                                                "ClientHandler-Pinging-Thread");
                                        pingThread.start();
                                        username = message[1];
                                        sendToClient(ServerCommands.sLOGIN());
                                    }
                                }
                            } else {
                                sendToClient(ServerCommands.sERROR(
                                        "HELLO protocol not initialized"));
                            }
                            break;
                        case "LIST":
                            if (initHello && initLogin) {
                                List<String> list = new ArrayList<>();
                                for (ClientHandler ch : gs.getClientHandlers()) {
                                    list.add(ch.getUsername());
                                }
                                sendToClient(ServerCommands.sLIST(list.toArray(new String[0])));
                            } else {
                                List<String> str = new ArrayList<>();
                                if (!initHello) {
                                    str.add("HELLO protocol not initialized");
                                }
                                if (!initLogin) {
                                    str.add("LOGIN protocol not initialized");
                                }
                                sendToClient(ServerCommands.sERROR(str.toArray(new String[0])));
                            }
                            break;
                        case "RANK":
                            if (initHello && initLogin) {
                                List<Map.Entry<String, Integer>> hashList = new ArrayList<>(
                                        gs.getGameHandler().getScore().entrySet());
                                hashList.sort(Map.Entry.comparingByValue());
                                List<String> list = new ArrayList<>();
                                for (Map.Entry<String, Integer> entry : hashList) {
                                    list.add("" + entry.getValue());
                                    list.add(entry.getKey());
                                }
                                Collections.reverse(list);
                                sendToClient(ServerCommands.sRANK(list.toArray(new String[0])));
                            } else {
                                List<String> str = new ArrayList<>();
                                if (!initHello) {
                                    str.add("HELLO protocol not initialized");
                                }
                                if (!initLogin) {
                                    str.add("LOGIN protocol not initialized");
                                }
                                sendToClient(ServerCommands.sERROR(str.toArray(new String[0])));
                            }
                            break;
                        case "QUEUE":
                            if (initHello && initLogin) {
                                gs.getGameHandler().getLock().lock();
                                gs.getGameHandler().addQueue(this);
                                while (!inGame) {
                                    gs.getGameHandler().getToQueue().signalAll();
                                    gs.getGameHandler().getToPlay().await();
                                    if (!inGame) {
                                        gs.getGameHandler().getToWaitAgain().await();
                                    }
                                    Thread.sleep((int) (Math.random() * 20));
                                }
                                gs.getGameHandler().getLock().unlock();
                            } else {
                                List<String> str = new ArrayList<>();
                                if (!initHello) {
                                    str.add("HELLO protocol not initialized");
                                }
                                if (!initLogin) {
                                    str.add("LOGIN protocol not initialized");
                                }
                                sendToClient(ServerCommands.sERROR(str.toArray(new String[0])));
                            }
                            break;
                        case "MOVE":
                            if (inGame) {
                                gs.getGameHandler().getLock().lock();
                                pwGame.println(stringBuilder);
                                gs.getGameHandler().getBoardSignal().await();
                                gs.getGameHandler().getLock().unlock();
                                Thread.sleep((int) (Math.random() * 20));
                            }
                            break;
                        case "PING":
                            if (initHello && initLogin) {
                                sendToClient(ServerCommands.sPONG());
                            } else {
                                List<String> str = new ArrayList<>();
                                if (!initHello) {
                                    str.add("HELLO protocol not initialized");
                                }
                                if (!initLogin) {
                                    str.add("LOGIN protocol not initialized");
                                }
                                sendToClient(ServerCommands.sERROR(str.toArray(new String[0])));
                            }
                            break;
                        case "PONG":
                            if (initHello && initLogin) {
                                pinging = true;
                            } else {
                                List<String> str = new ArrayList<>();
                                if (!initHello) {
                                    str.add("HELLO protocol not initialized");
                                }
                                if (!initLogin) {
                                    str.add("LOGIN protocol not initialized");
                                }
                                sendToClient(ServerCommands.sERROR(str.toArray(new String[0])));
                            }
                            break;
                        case "QUIT":
                            sendToClient(ServerCommands.sQUIT());
                            gs.removeClient(this);
                            return;
                    }
                }
            }
        } catch (IOException | NullPointerException | InterruptedException e) {
//            e.printStackTrace();
        }
        gs.removeClient(this);
    }
}
