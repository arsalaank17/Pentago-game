package gamelogic.player;

import gamelogic.board.Board;

import java.io.*;

/**
 * Class for maintaining a Network player in Pentago.
 * Module 2 project. Network player refers to
 * a player playing online.
 * @author Kevin Schurman and Arsalaan Khan
 */
public class NetworkPlayer extends Player {
    private final PipedReader in;
    private PrintWriter out;

    private final StringBuilder inData = new StringBuilder();

    /**
     * Creates a new Network player object. A network
     * player is a player playing online connected to
     * a server!
     * @param name The name of the network player.
     * @param in The PipedReader the network player will be
     *           using to read incoming data.
     * @param mark The mark of the network player.
     * @param out The PrintWriter the network player will
     *            be using to send his move to the server.
     */
    public NetworkPlayer(String name, PipedReader in, Mark mark, PrintWriter... out) {
        super(name, mark);
        this.in = in;
        if (out != null && out.length > 0) {
            this.out = out[0];
        }
    }

    /**
     * The method used to access the PipedReader
     * which reads incoming data.
     * @return The PipedReader used to
     * get read the incoming data from the
     * server
     */
    public PipedReader getIn() {
        return in;
    }

    /**
     * The method used to access the PrintWriter
     * which is used to send the data to the server.
     * @return The printWriter used to send
     * the data to the server.
     */
    public PrintWriter getOut() {
        return out;
    }

    /**
     * Method used to get the Move sent by the
     * server by processing it.
     * @return an integer array with the
     * move sent by the server including the move
     * index and the rotation.
     */
    public Integer[] getInData() {
        try {
            inData.setLength(0);
            char c;
            while ((c = (char) in.read()) != '\n') {
                if (c != '\r') {
                    inData.append(c);
                }
            }
            String msg = inData.toString();
            String[] inSplit = msg.split("~");
            if (inSplit[0].equals("MOVE") && inSplit.length == 3) {
                return new Integer[]{Integer.parseInt(inSplit[1]), Integer.parseInt(inSplit[2])};
            } else {
                throw new IOException("ERROR WITH MOVE");
            }
        } catch (IOException e) {
//            e.printStackTrace();
        }
        return null;
    }

    @Override
    public int determineMove(Board board) {
        return -1;
    }

    @Override
    public int determineRotation(Board board) {
        return -1;
    }
}
