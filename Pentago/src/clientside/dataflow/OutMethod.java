package clientside.dataflow;

import clientside.client.Client;
import clientside.client.ClientMethod;
import commands.ClientCommands;

import java.io.IOException;
import java.io.InterruptedIOException;
import java.io.PipedReader;
import java.io.PrintWriter;

/**
 * The class responsible for the messages the client
 * has to send to the server hosting the Pentago game!
 * @author Kevin Schurman and Arsalaan Khan
 */
public class OutMethod implements Runnable {
    private final ClientMethod clientMethod;
    private final PrintWriter dataOut;
    private final PipedReader pprOut;
    private boolean running = false;

    /**
     * The constructor for the outMethod class!
     * Creates a new OutMethod object!
     * Takes in the client, a printWriter and a
     * PipedReader as parameters!
     * @param clientMethod - The client object
     *                     that is connected
     * @param dataOut - The PrintWriter used to send
     *                the data to the server
     * @param pprOut - The PipedReader used to receive
     *               the messages from the server
     */
    public OutMethod(Client clientMethod, PrintWriter dataOut, PipedReader pprOut) {
        this.clientMethod = (ClientMethod) clientMethod;
        this.dataOut = dataOut;
        this.pprOut = pprOut;
    }

    /**
     * This method is used to send data to the server!
     * It uses the client's printWriter's println
     * function to send over the messages!
     * @param toSend the string representing the data
     *               which has to be sent over to the
     *               server
     */
    private void sendToServer(String toSend) {
        dataOut.println(toSend);
    }

    /**
     * This method is used to decide what messages
     * are to be sent out to the server. This method
     * is essential because a particular protocol has
     * to be followed with the messages to the server
     * so that the server can recognise the messages sent
     * and respond accordingly
     * @param msg the String msg to be sent over to the
     *            server!
     * @return true if the message was sent successfully and
     * false otherwise.
     */
    public boolean sendMessage(String msg) {
        String message = null;
        String[] messageSplit = msg.replace("\r", "").split(" ");
        if (!clientMethod.isInGaming()) { // To client - In Lobby
            switch (messageSplit[0].toUpperCase()) {
                case "HELP":
                    clientMethod.getUsrOut().println("HELP - Lobby");
                    clientMethod.getUsrOut().println("\tServer Communicating Commands:");
                    clientMethod.getUsrOut().println("\t\tLOGIN - Logins in to the server.");
                    clientMethod.getUsrOut().println("\t\tLIST "
                            + "- Shows a list of players currently connected to the server.");
                    clientMethod.getUsrOut().println("\t\tRANK "
                            + "- Shows a list of ranking players in terms of score in order.");
                    clientMethod.getUsrOut().println("\t\tQUEUE - "
                            + "Queues in for a game to play against other players.");
                    clientMethod.getUsrOut().println("\t\tMOVE - "
                            + "While in game and its your turn, allows for you to make a move.");
                    clientMethod.getUsrOut().println("\t\tQUIT - Quits the application.");
                    clientMethod.getUsrOut().println("\tClientSide Commands:");
                    clientMethod.getUsrOut().println("\t\t-H - "
                            + "Normal input is what will happen when playing against others.");
                    clientMethod.getUsrOut().println("\t\t-N - "
                            + "A computer bot will play for you and make random choices.");
                    clientMethod.getUsrOut().println("\t\t-S - "
                            + "A computer bot will play for you and make smarter choices.");
                    clientMethod.getUsrOut().println("\t\tHELP (in lobby) - "
                            + "Shows relevant helping related problems and client commands "
                            + "for communication with server/client.");
                    clientMethod.getUsrOut().println("\t\tHELP (in game) - "
                            + "Shows game related help related problems and client commands on "
                            + "how to do specific game related tasks.");
                    clientMethod.getUsrOut().println("\t\tHINT (in game) - "
                            + "Gives a minor help for the user to use if they have no "
                            + "other idea to use so.");
                    clientMethod.getUsrOut().println("\t\tROTATION (in game) - "
                            + "Show information on what numbers do what when rotation a piece "
                            + "of the board.");
                    break;
                case "-H":
                    clientMethod.getUsrOut().println("Now using normal human input.");
                    clientMethod.setMyOwnPlayer('h');
                    break;
                case "-N":
                    clientMethod.getUsrOut().println("Now using naive strategy.");
                    clientMethod.setMyOwnPlayer('n');
                    break;
                case "-S":
                    clientMethod.getUsrOut().println("Now using smart strategy.");
                    clientMethod.setMyOwnPlayer('s');
                    break;
            }
        } else { // To client - In Game
            switch (messageSplit[0].toUpperCase()) {
                case "HELP":
                    clientMethod.getUsrOut().println("HELP - InGame");
                    clientMethod.getUsrOut().println("\tInput Information:");
                    clientMethod.getUsrOut().println("\t\tWhen making an input to play the game, "
                            + "you will need to input numbers of the Row, Col, and Rotation, "
                            + "separated by spaces in the order of \"ROW COL ROTATION\", "
                            + "for example;"
                            + "\n\t\t1 2 3");
                    clientMethod.getUsrOut().println("\t\tROW - "
                            + "input a number from 0 to 5 as according to the board shown.");
                    clientMethod.getUsrOut().println("\t\tCOL - "
                            + "input a number from 0 to 5 as according to the board shown.");
                    clientMethod.getUsrOut().println("\t\tROTATION - "
                            + "input a number from 0 to 7 to rotate specific parts of the board."
                            + "\n\t\t(Use \"ROTATION\" to see more details on what specific "
                            + "numbers do)");
                    clientMethod.getUsrOut().println("\tClientSide Commands:");
                    clientMethod.getUsrOut().println("\t\tHELP - "
                            + "To see more detailed information on what function does what.");
                    clientMethod.getUsrOut().println("\t\tROTATION - "
                            + "To see more detailed information on rotation numbers.");
                    clientMethod.getUsrOut().println("\t\tHINT - "
                            + "To be given a minor help for an empty field.");
                    break;
                case "HINT":
                    Integer[] data = clientMethod.getGame().getBoard().indexToRowCol(
                            clientMethod.getGame().getBoard().getHint());
                    clientMethod.getUsrOut().println("Here's a hint: "
                            + "Row-" + data[0] + " Col-" + data[1]);
                    break;
                case "ROTATION":
                    clientMethod.getUsrOut().println("\tRotation Information:");
                    clientMethod.getUsrOut().println("\t\t0 - rotates the top left "
                            + "sub-board counter-clockwise");
                    clientMethod.getUsrOut().println("\t\t1 - rotates the top left "
                            + "sub-board clockwise");
                    clientMethod.getUsrOut().println("\t\t2 - rotates the top right "
                            + "sub-board counter-clockwise");
                    clientMethod.getUsrOut().println("\t\t3 - rotates the top right "
                            + "sub-board clockwise");
                    clientMethod.getUsrOut().println("\t\t4 - rotates the bottom left "
                            + "sub-board counter-clockwise");
                    clientMethod.getUsrOut().println("\t\t5 - rotates the bottom left "
                            + "sub-board clockwise");
                    clientMethod.getUsrOut().println("\t\t6 - rotates the bottom right "
                            + "sub-board counter-clockwise");
                    clientMethod.getUsrOut().println("\t\t7 - rotates the bottom right "
                            + "sub-board clockwise");
                    break;
                default:
                    try {
                        if (clientMethod.getOurPlayer() == clientMethod.getCurrentPlayer()
                                && messageSplit.length == 3
                                && clientMethod.getMyOwnPlayer() == 'h') {
                            messageSplit = new String[]{"MOVE",
                                "" + clientMethod.getGame().getBoard().index(
                                        Integer.parseInt(messageSplit[0]),
                                        Integer.parseInt(messageSplit[1])),
                                "" + Integer.parseInt(messageSplit[2])
                            };
                        }
                    } catch (NumberFormatException e) {
                        if (clientMethod.isDebug()) {
                            e.printStackTrace();
                        }
                        clientMethod.getUsrOut().println("Wrong input. Please use valid numbers.");
                    }
                    break;
            }
        }
        switch (messageSplit[0].toUpperCase()) { // To server
            case "HELLO":
                message = ClientCommands.cHELLO(
                        clientMethod.getClientName(), clientMethod.getSupportedExtensions());
                break;
            case "LOGIN":
                message = ClientCommands.cLOGIN(clientMethod.getUsername());
                break;
            case "LIST":
                message = ClientCommands.cLIST();
                break;
            case "RANK":
                message = ClientCommands.cRANK();
                break;
            case "QUEUE":
                if (!clientMethod.isQueuing()) {
                    clientMethod.setQueuing(true);
                    message = ClientCommands.cQUEUE();
                    clientMethod.getUsrOut().println("Currently in Queue.");
                }
                break;
            case "MOVE":
                if (clientMethod.isInGaming() && messageSplit.length == 3) {
                    if (clientMethod.getGame().getBoard().isField(Integer.parseInt(messageSplit[1]))
                            && clientMethod.getGame().getBoard().isEmptyField(
                                    Integer.parseInt(messageSplit[1]))
                            && clientMethod.getGame().getBoard().isRotation(
                                    Integer.parseInt(messageSplit[2]))) {
                        message = ClientCommands.cMOVE(
                                Integer.parseInt(messageSplit[1]),
                                Integer.parseInt(messageSplit[2]));
                    } else {
                        clientMethod.getUsrOut().println("Error with input. "
                                + "Please write correct values.");
                        clientMethod.getUsrOut().println("Use \"HELP\" if needed.");
                    }
                }
                break;
            case "PING":
                message = ClientCommands.cPING();
                break;
            case "PONG":
                message = ClientCommands.cPONG();
                break;
            case "QUIT":
                message = ClientCommands.cQUIT();
                clientMethod.getUsrOut().println("SENDING: " + msg);
                sendToServer(message);
                return false;
        }
        if (message != null) {
            if (clientMethod.isDebug()) {
                clientMethod.getUsrOut().println("SENDING: " + message);
            }
            sendToServer(message);
        }
        return true;
    }

    /**
     * The run method of the OutMethod class.
     * The run() method can be called using the start() method
     * to have multiple threads of this class. When this method
     * is called , the code below is executed which is responsible
     * to send the data to the server and print some important information
     * for the client!
     */
    @Override
    public void run() {
        try {
            if (!running) {
                running = true;
                Thread thread = new Thread(this, "Thread-Out-Running");
                thread.start();
                try {
                    while (true) {
                        StringBuilder str = new StringBuilder();
                        char c;
                        while ((c = (char) pprOut.read()) != '\n') {
                            str.append(c);
                        }
                        if (!sendMessage(str.toString())) {
                            break;
                        }
                    }
                } catch (InterruptedIOException e) {
                    if (clientMethod.isDebug()) {
                        e.printStackTrace();
                    }
                }
                thread.interrupt();
            } else {
                boolean exit = false;
                do {
                    clientMethod.getLock().lock();
                    clientMethod.getGaming().await();
                    if (clientMethod.getMyOwnPlayer() == 'n'
                            || clientMethod.getMyOwnPlayer() == 's') {
                        while (clientMethod.isInGaming()) {
                            clientMethod.getInCondition().await();
                            if (!clientMethod.isInGaming()) {
                                break;
                            }
                            if (clientMethod.getCurrentPlayer() == clientMethod.getOurPlayer()) {
                                int move;
                                int rotation;
                                move = clientMethod.getOwnStrategy().determineMove(
                                        clientMethod.getGame().getBoard().deepCopy(),
                                        clientMethod.getGame().getCurrent().getMark());
                                rotation = clientMethod.getOwnStrategy().determineRotation(
                                        clientMethod.getGame().getBoard().deepCopy(),
                                        clientMethod.getGame().getCurrent().getMark());
                                String command = "MOVE " + move + " " + rotation;
                                if (!sendMessage(command)) {
                                    exit = true;
                                    break;
                                }
                            }
                        }
                    }
                    clientMethod.getLock().unlock();
                } while (!exit);
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
