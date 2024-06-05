package clientside.dataflow;

import clientside.client.Client;
import clientside.client.ClientMethod;
import gamelogic.player.Mark;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.PrintWriter;

/**
 * The class responsible for the messages
 * the client receives from the server hosting
 * the Pentago game and doing specific tasks depending
 * on the message received from the server!
 * @author Kevin Schurman and Arsalaan Khan
 */
public class InMethod implements Runnable {
    private final PrintWriter pw;
    private final BufferedReader in;
    private final ClientMethod clientMethod;
    private boolean running = false;

    /**
     * The constructor for the InMethod class!
     * Creates a new InMethod object!
     * Takes in the client, a bufferedReader
     * and a printWriter as parameters!
     * @param clientMethod - The client object
     *                     that is connected
     * @param in - The BufferedReader used to read
     *           messages sent from the server!
     * @param pw - The printWriter used to send messages to
     *           the server
     */
    public InMethod(Client clientMethod, BufferedReader in, PrintWriter pw) {
        this.clientMethod = (ClientMethod) clientMethod;
        this.in = in;
        this.pw = pw;
    }

    private boolean receiveMessage(String message) {
        if (clientMethod.isDebug()) {
            clientMethod.getUsrOut().println("RECEIVED: " + message);
        }
        try {
            String[] msg = message.split("~");
            switch (msg[0].toUpperCase()) {
                case "HELLO":
                    pw.println("[SERVER] : " + msg[0] + " " + msg[1]);
                    if (msg.length == 3) {
                        pw.println(" " + "The supported extensions are" + msg[2]);
                    } else if (msg.length == 4) {
                        pw.println("The supported extensions are"
                                + msg[2] + " and " + msg[3]);
                    }
                    clientMethod.getLock().lock();
                    clientMethod.getHelloed().signalAll();
                    clientMethod.getLock().unlock();
                    break;
                case "LOGIN":
                    pw.println("Login successful!");
                    clientMethod.getLock().lock();
                    clientMethod.setLoggedIn(true);
                    clientMethod.getLogged().signalAll();
                    clientMethod.getLock().unlock();
                    break;
                case "ALREADYLOGGEDIN":
                    pw.println("The user is already logged in!");
                    clientMethod.getLock().lock();
                    clientMethod.getLogged().signalAll();
                    clientMethod.getLock().unlock();
                    break;
                case "LIST":
                    pw.println("Here is a list of the players connected right now: ");
                    for (int i = 1; i < msg.length; i++) {
                        pw.println("-\t" + msg[i]);
                    }
                    break;
                case "RANK":
                    pw.println("Here is the player ranking list right now: ");
                    for (int i = 1; i < msg.length; i += 2) {
                        pw.println("-\t" + msg[i] + " | " + msg[i + 1]);
                    }
                    break;
                case "NEWGAME":
                    pw.println("The new game is starting between the users : [" + msg[1]
                            + "] and [" + msg[2] + "]. May the best player win!");
                    if (!clientMethod.newGame(msg[1], msg[2])) {
                        return false;
                    }
                    clientMethod.setInGaming(true);
                    clientMethod.getLock().lock();
                    clientMethod.getGaming().signalAll();
                    clientMethod.getLock().unlock();
                    clientMethod.getUsrOut().println(clientMethod.getGame().getBoard().toString());
                    break;
                case "MOVE":
                    if (clientMethod.getOurPlayer() == clientMethod.getCurrentPlayer()) {
                        String[] str = message.split("~");
                        Integer[] data = clientMethod.getGame().getBoard().indexToRowCol(
                                Integer.parseInt(str[1]));
                        clientMethod.getPwGame().println(data[0] + " " + data[1]);
                        clientMethod.getPwGame().println(str[2]);
                    } else {
                        clientMethod.getPwGameNet().println(message);
                    }
                    clientMethod.setCurrentPlayer(1 - clientMethod.getCurrentPlayer());
                    clientMethod.getLock().lock();
                    clientMethod.getOurTurn().signalAll();
                    clientMethod.getLock().unlock();
                    break;
                case "GAMEOVER":
                    clientMethod.setQueuing(false);
                    clientMethod.setInGaming(false);
                    clientMethod.getLock().lock();
                    clientMethod.getOurTurn().signalAll();
                    clientMethod.getInCondition().signalAll();
                    clientMethod.getLock().unlock();
                    Thread.sleep(50);
                    clientMethod.getUsrOut().println(clientMethod.getGame().getBoard().toString());
                    clientMethod.getUsrOut().println(clientMethod.getGame().result());
                    switch (msg[1]) {
                        case "VICTORY":
                            pw.println("Game is now over because we have a winner!"
                                    + " Congratulations to " + msg[2] + " for winning the game!");
                            break;
                        case "DISCONNECT":
                            pw.println("Game is now over because of a disconnect!"
                                    + " Congratulations to " + msg[2] + " for winning the game!");
                            break;
                        case "DRAW":
                            pw.println("Game is now over because we have a draw!");
                            break;
                    }
                    clientMethod.getUsrOut().println("It took "
                            + clientMethod.getGame().getMoves() + " moves for this game to end.");
                    break;
                case "PING":
                    clientMethod.getMOutMethod().sendMessage("PONG");
                    break;
                case "PONG":
                    break;
                case "ERROR":
                    if (clientMethod.isInGaming()) {
                        clientMethod.getLock().lock();
                        clientMethod.getOurTurn().signalAll();
                        clientMethod.getLock().unlock();
                        try {
                            clientMethod.getUsrOut().println("MAKING SURE: " + in.readLine());
                        } catch (IOException e) {
                            if (clientMethod.isDebug()) {
                                e.printStackTrace();
                            }
                        }
                    }
                    break;
                case "QUIT":
                    pw.println("The server has asked to quit! Goodbye!");
                    return false;
            }
            return true;
        } catch (NullPointerException | InterruptedException e) {
            if (clientMethod.isDebug()) {
                e.printStackTrace();
            }
            return false;
        }
    }

    /**
     * The run method of the InMethod class.
     * The run() method can be called using the start() method
     * to have multiple threads of this class. When this method
     * is called , the code below is executed which is mainly
     * responsible for informing the client about what is the situation
     * in the game
     */
    @Override
    public void run() {
        try {
            if (!running) {
                running = true;
                Thread thread = new Thread(this, "Thread-In-Running");
                thread.start();
                while (true) {
                    if (!receiveMessage(in.readLine())) {
                        break;
                    }
                }
                thread.interrupt();
            } else {
                while (true) {
                    clientMethod.getLock().lock();
                    clientMethod.getGaming().await();

                    String colour = (clientMethod.getGame().getCurrent().getMark() == Mark.WHITE
                            ? (char) 27 + "[30;47;1m (White) " : (char) 27 + "[37;40;1m (Black) ")
                            + (char) 27 + "[0m";
                    if (clientMethod.getOurPlayer() == clientMethod.getCurrentPlayer()) {
                        pw.println(colour + " Your Turn");
                        if (clientMethod.getMyOwnPlayer() == 'h') {
                            pw.println("ROW COL ROTATION");
                        }
                        clientMethod.getInCondition().signalAll();
                    } else {
                        pw.println(colour + " Opponents Turn");
                    }

                    while (clientMethod.isInGaming()) {
                        try {
                            clientMethod.getShowBoard().await();
                            pw.println(clientMethod.getGame().getBoard().toString());
                        } catch (InterruptedException e) {
                            if (clientMethod.isDebug()) {
                                e.printStackTrace();
                            }
                        }

                        if (!clientMethod.isInGaming()) {
                            break;
                        }

                        colour = (clientMethod.getGame().getCurrent().getMark() == Mark.WHITE
                                    ? (char) 27 + "[30;47;1m (White) "
                                    : (char) 27 + "[37;40;1m (Black) ")
                                + (char) 27 + "[0m";
                        if (clientMethod.getOurPlayer() == clientMethod.getCurrentPlayer()) {
                            pw.println(colour + " Your Turn");
                            if (clientMethod.getMyOwnPlayer() == 'h') {
                                pw.println("ROW COL ROTATION");
                            }
                            clientMethod.getInCondition().signalAll();
                        } else {
                            pw.println(colour + " Opponents Turn");
                        }
                        clientMethod.getOurTurn().await();
                    }
                    clientMethod.getLock().unlock();
                }
            }
        } catch (IOException | InterruptedException e) {
            if (clientMethod.isDebug()) {
                e.printStackTrace();
            }
        }
        clientMethod.getLock().lock();
        clientMethod.getDeadServer().signalAll();
        clientMethod.getLock().unlock();
    }
}
