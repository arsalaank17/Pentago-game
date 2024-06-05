package clientside.client;

import clientside.dataflow.InMethod;
import clientside.dataflow.OutMethod;
import gamelogic.computer.Strategy;
import gamelogic.computer.StrategyFactory;
import gamelogic.computer.StrategyFactoryMethod;
import gamelogic.game.Game;
import gamelogic.game.GameMethod;
import gamelogic.player.*;

import java.io.*;
import java.net.InetAddress;
import java.net.Socket;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;

/**
 * The class representing a client connected to a
 * server hosting the Pentago game!
 * @author Kevin Schurman and Arsalaan Khan
 */
public class ClientMethod implements Client, Runnable {
    private final String clientName = "Arsalaan and Kevin's Client";
    private final String[] supportedExtensions = new String[]{"RANK"};
    private boolean debug = false;
    private String username = null;

    private final ReentrantLock reentrantLock = new ReentrantLock();
    private final Condition helloed = reentrantLock.newCondition();
    private final Condition logged = reentrantLock.newCondition();
    private final Condition gaming = reentrantLock.newCondition();
    private final Condition showBoard = reentrantLock.newCondition();
    private boolean loggedIn = false;
    private boolean queuing = false;
    private boolean inGaming = false;
    private final Condition ourTurn = reentrantLock.newCondition();
    private final Condition inCondition = reentrantLock.newCondition();
    private final Condition deadServer = reentrantLock.newCondition();

    private final BufferedReader usrInp;
    private final PrintWriter usrOut;

    private Socket socket;
    private Game game;
    private int ourPlayer;
    private int currentPlayer;
    private char myOwnPlayer = 'h';

    private Strategy ownStrategy;

    private BufferedReader dataIn;
    private PrintWriter pwIn;
    private Thread tIn;

    private PrintWriter dataOut;
    private PipedReader pprOut;
    private PipedWriter ppwOut;
    private PrintWriter pwOut;
    private OutMethod mOutMethod;
    private Thread tOut;

    private PipedReader pprGame;
    private PipedWriter ppwGame;
    private PrintWriter pwGame;

    private PipedReader pprGameNet;
    private PipedWriter ppwGameNet;
    private PrintWriter pwGameNet;

    /**
     * This method is used to create a client object!
     * @param br This is the buffered reader that the client
     *           would use to read the incoming data
     * @param pw This is the printWriter that the client would
     *           use to send the data to the server!
     * @param args arguments made from the client
     */
    public ClientMethod(BufferedReader br, PrintWriter pw, String[] args) {
        usrInp = br;
        usrOut = pw;
        for (String arg : args) {
            if (arg.equals("--debug")) {
                debug = true;
                break;
            }
        }
    }

    /**
     * This method is used to access the condition
     * Helloed which indicates if the client and
     * server have exchanged hello's!
     * @return Condition Helloed
     */
    public Condition getHelloed() {
        return helloed;
    }

    /**
     * This method allows for further information
     * to be present to allow for better debugging
     * purposes.
     * @return boolean for debugging
     */
    public boolean isDebug() {
        return debug;
    }

    /**
     * This method is used to access the condition
     * Helloed which indicates if the client has
     * successfully logged into the server!
     * @return Condition getLogged
     */
    public Condition getLogged() {
        return logged;
    }

    /**
     * This method is used to access the condition
     * gaming which indicates if the client is in
     * a game of Pentago!
     * @return Condition gaming
     */
    public Condition getGaming() {
        return gaming;
    }

    /**
     * This method is used to set the boolean loggedIn
     * to true oor false depending on if the client has
     * logged in to the server or not!
     * @param bool Represents the login status of a client
     */
    public void setLoggedIn(boolean bool) {
        this.loggedIn = bool;
    }

    /**
     * This method is used to access the boolean isInGaming
     * which indicates if a client is in a game of pentago
     * or not!
     * @return inGaming which is true if a client is in a
     * game and false otherwise.
     */
    public boolean isInGaming() {
        return inGaming;
    }

    /**
     * This method is used to set the boolean inGaming
     * to true if a client is in a game and to false otherwise.
     * @param bool indicating if a client is in a game or not
     */
    public void setInGaming(boolean bool) {
        this.inGaming = bool;
    }

    /**
     * This method is used to check if the server connected is dead.
     * @return deadServer which signals if the server connected is dead
     */
    public Condition getDeadServer() {
        return deadServer;
    }

    /**
     * This method is used to access the condition ourTurn
     * which indicates if it is this client's turn.
     * @return ourTurn which indicates if it's the client's turn.
     */
    public Condition getOurTurn() {
        return ourTurn;
    }

    /**
     * This method is used to access the condition inCondition
     * which indicates if it is the client should now read the
     * data received.
     * @return inCondition which indicates if client should now
     * read the incoming data
     */
    public Condition getInCondition() {
        return inCondition;
    }

    /**
     * This method is used to access the PrintWriter usrOut
     * which is the print writer used by the client to send
     * the data to the server.
     * @return usrOut which is used to send the data to the
     * server
     */
    public PrintWriter getUsrOut() {
        return usrOut;
    }

    /**
     * This method is used to access the int ourPlayer which
     * is an int representing the current client playing
     * the game.
     * @return ourPlayer an int representing the current client
     */
    public int getOurPlayer() {
        return ourPlayer;
    }

    /**
     * This method is used to set the player that they want to
     * use during a game. They can either use a human player,
     * naive random strategy, or a smarter strategy.
     * @param myOwnPlayer for the player strategy type
     */
    public void setMyOwnPlayer(char myOwnPlayer) {
        this.myOwnPlayer = myOwnPlayer;
    }

    /**
     * This method is used to access the char myOwnPlayer which
     * is a char representing the current client playing
     * the game. Used to differentiate between a human player,
     * Naive AI player and the Smart AI player
     * @return myOwn player which is a char representing
     * this client depending on the type of player they are.
     */
    public char getMyOwnPlayer() {
        return myOwnPlayer;
    }

    /**
     * This method is used to access the reentrant lock
     * used by the client thread. Locks are used to allow
     * only one thread to access a critical section
     * at one time to avoid concurrency issues.
     * @return the ReentrantLock used to ensure a thread-
     * safe program.
     */
    public ReentrantLock getLock() {
        return this.reentrantLock;
    }

    /**
     * This method returns the strategy that the player
     * has inputted, whether they choose to play for themselves
     * or let a bot play for them.
     * @return strategy player has chosen
     */
    public Strategy getOwnStrategy() {
        return ownStrategy;
    }

    /**
     * This method returns the out server data flow
     * for sending.
     * @return outMethod for out data flow
     */
    public OutMethod getMOutMethod() {
        return mOutMethod;
    }

    /**
     * Sets the queuing boolean to indicate whether
     * the player is currently attempting to queue up for a game.
     * @param queuing boolean if wanting to play
     */
    public void setQueuing(boolean queuing) {
        this.queuing = queuing;
    }

    /**
     * Gets the queuing boolean to see if that player
     * is indicating that they want to be able to play
     * a game.
     * @return boolean if they want to play
     */
    public boolean isQueuing() {
        return queuing;
    }

    /**
     * Sets the current player such that the user can
     * be in track of the current player that is playing.
     * @param currentPlayer of the game
     */
    public void setCurrentPlayer(int currentPlayer) {
        this.currentPlayer = currentPlayer;
    }

    /**
     * Gets the current player such that the user can
     * see who is currently playing the game right now.
     * @return int of the current player
     */
    public int getCurrentPlayer() {
        return currentPlayer;
    }

    /**
     * The condition of showBoard is used to communicate with
     * the game to see whether the client should display the board.
     * @return condition of the board state
     */
    public Condition getShowBoard() {
        return showBoard;
    }

    /**
     * This method gives a boolean value depending on
     * whether the 2 players passed as the parameter can
     * get in a game or not!
     * @param player1 - The first player who is going to be in the game!
     * @param player2 - The second player of the game!
     * @return true if the players can get in a game and false if
     * an error happened.
     */
    @Override
    public boolean newGame(String player1, String player2) {
        try {
            pprGame = new PipedReader();
            ppwGame = new PipedWriter(pprGame);
            pwGame = new PrintWriter(ppwGame, true);

            pprGameNet = new PipedReader();
            ppwGameNet = new PipedWriter(pprGameNet);
            pwGameNet = new PrintWriter(ppwGameNet);

            Player[] ps = new Player[2];
            Mark[] marks = new Mark[]{Mark.WHITE, Mark.BLACK};
            String[] players = new String[]{player1, player2};
            PlayerFactory pf = new PlayerFactoryMethod();
            StrategyFactory sf = new StrategyFactoryMethod();
            for (int i = 0; i < 2; i++) {
                if (players[i].equals(username)) {
                    switch (myOwnPlayer) {
                        case 'h':
                            ps[i] = pf.makeHumanPlayer(username, pprGame, marks[i]);
                            break;
                        case 'n':
                            ownStrategy = sf.makeNaiveStrategy();
                            ps[i] = pf.makeHumanPlayer(username, pprGame, marks[i]);
                            break;
                        case 's':
                            ownStrategy = sf.makeSmartStrategy();
                            ps[i] = pf.makeHumanPlayer(username, pprGame, marks[i]);
                            break;
                    }
                    ourPlayer = i;
                } else {
                    ps[i] = pf.makeNetworkPlayer(players[i], pprGameNet, marks[i]);
                }
            }
            currentPlayer = 0;
            game = new GameMethod(ps[0], ps[1], reentrantLock, showBoard);
            new Thread((Runnable) game, "Game-Thread").start();
            return true;
        } catch (IOException e) {
            if (debug) {
                e.printStackTrace();
            }
            return false;
        }
    }

    /**
     * This method is used to access
     * the PrintWriter object that is used in the game!
     * @return A printWriter object used in game.
     */
    @Override
    public PrintWriter getPwGame() {
        return pwGame;
    }

    /**
     * This method is used to access another
     * PrintWriter object that is used in the game!
     * @return A printWriter object used in game.
     */
    @Override
    public PrintWriter getPwGameNet() {
        return pwGameNet;
    }

    /**
     * This method is used to access the game object
     * used by a client when in a game of pentago!
     * @return The game object when a client
     * is in a game.
     */
    @Override
    public Game getGame() {
        return game;
    }

    /**
     * This method is used to access the client's
     * name!
     * @return The string representing the client's name.
     */
    @Override
    public String getClientName() {
        return clientName;
    }

    /**
     * This method is used to access the client's
     * username in the game!
     * @return The string representing the client's
     * username.
     */
    @Override
    public String getUsername() {
        return username;
    }

    /**
     * This method is used to access the supported
     * extensions of the server the client is connected to!
     * @return The string[] representing all the extensions
     * the server supports
     */
    @Override
    public String[] getSupportedExtensions() {
        return supportedExtensions;
    }

    /**
     * This method is used to start the client
     * thread! A client is connected to the server
     * and can access various commands to play the
     * Pentago game!
     */
    @Override
    public void start() {
        if (!System.getProperty("os.name").equals("Linux")) {
            usrOut.println(((char) 27 + "[30;41;1m") + "NOTICE: It is required that this client is used in the "
                    + "Linux platform as the Unix/Linux's system makes it more "
                    + "stable and consistent than over " + System.getProperty("os.name") +".\n" + ((char) 27 + "[0m"));
        }
        usrOut.println("Currently using " + clientName);
        InetAddress address = null;
        int port = -1;

        while (socket == null) {
            usrOut.printf("Please provide an IP address or hostname" +
                          "(or leave blank for localhost): ");
            do {
                try {
                    String str = usrInp.readLine();
                    if (str.equals("")) {
                        address = InetAddress.getByName("localhost");
                    } else {
                        address = InetAddress.getByName(str);
                    }
                } catch (IOException e) {
                    if (debug) {
                        e.printStackTrace();
                    }
                    usrOut.println("InetAddress of server name gives error. "
                            + "Check if your input is valid.");
                }
            } while (address == null);

            usrOut.printf("Please provide a port number (or leave blank for 55555): ");
            do {
                try {
                    String str = usrInp.readLine();
                    if (str.equals("")) {
                        port = 55555;
                    } else {
                        port = Integer.parseInt(str);
                    }
                } catch (IOException e) {
                    if (debug) {
                        e.printStackTrace();
                    }
                    usrOut.println("Incorrect port number input.");
                }
            } while (!(port >= 0 && port <= 65535));

            try {
                socket = new Socket(address, port);
            } catch (IOException e) {
                if (debug) {
                    e.printStackTrace();
                }
                usrOut.println("Connection has been refused. Check if your input is valid.");
            }
        }

        try {
            dataIn = new BufferedReader(new InputStreamReader(socket.getInputStream()));
            pwIn = new PrintWriter(System.out, true);

            dataOut = new PrintWriter(socket.getOutputStream(), true);
            pprOut = new PipedReader();
            ppwOut = new PipedWriter(pprOut);
            pwOut = new PrintWriter(ppwOut, true);
        } catch (IOException e) {
            if (debug) {
                e.printStackTrace();
            }
        }

        InMethod mInMethod = new InMethod(this, dataIn, pwIn);
        tIn = new Thread(mInMethod, "Thread-In");

        mOutMethod = new OutMethod(this, dataOut, pprOut);
        tOut = new Thread(mOutMethod, "Thread-Out");

        tIn.start();
        tOut.start();

        if (!mOutMethod.sendMessage("HELLO")) {
            return;
        }

        try {
            reentrantLock.lock();
            helloed.await();
            reentrantLock.unlock();
        } catch (InterruptedException e) {
            if (debug) {
                e.printStackTrace();
            }
        }

        while (!loggedIn) {
            try {
                reentrantLock.lock();
                usrOut.printf("Please input a username: ");
                String str = usrInp.readLine();
                if (!str.equals("")) {
                    username = str;
                    mOutMethod.sendMessage("LOGIN " + username);
                    logged.await();
                }
                reentrantLock.unlock();
            } catch (IOException | InterruptedException e) {
                if (debug) {
                    e.printStackTrace();
                }
            }
        }

        new Thread(this, "Awaiting-Dead-Server-Thread").start();

        usrOut.println("You can now start inputting commands.");
        usrOut.println("Use \"HELP\" if you need any.");
        String inpStr;
        try {
            do {
                inpStr = usrInp.readLine();
                pwOut.println(inpStr);
            } while (!(inpStr.equals("QUIT")));
        } catch (IOException e) {
            if (debug) {
                e.printStackTrace();
            }
        }
        reentrantLock.lock();
        deadServer.signalAll();
        reentrantLock.unlock();
    }

    @Override
    public void run() {
        try {
            reentrantLock.lock();
            deadServer.await();
            reentrantLock.unlock();
        } catch (InterruptedException e) {
            if (debug) {
                e.printStackTrace();
            }
        }

        usrOut.println("Server is disconnected or an error has occurred. Exiting...");
        System.exit(1);

        tIn.interrupt();
        tOut.interrupt();

        try {
            usrInp.close();
            usrOut.close();

            socket.close();

            dataIn.close();
            pwIn.close();

            dataOut.close();
            pwOut.close();
            ppwOut.close();
            pprOut.close();

            pwGame.close();
            ppwGame.close();
            pprGame.close();

            pwGameNet.close();
            ppwGameNet.close();
            pprGameNet.close();
        } catch (IOException e) {
            if (debug) {
                e.printStackTrace();
            }
        }
    }
}
