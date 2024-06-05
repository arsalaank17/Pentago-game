package commands;

/**
 * The class containing the client commands
 * following the protocol specified to us
 * in the project description!
 * @author Kevin Schurman and Arsalaan Khan
 */
public class ClientCommands {

    /**
     * The method responsible for returning
     * the hello message which is to be
     * sent by the client to the server.
     * @param description - The client description
     * @param extension - The extensions the client supports
     * @return a String which contains the
     * hello message to be sent according to the
     * protocol
     */
    public static String cHELLO(String description, String... extension) {
        return "HELLO" + "~" + description
                + (extension.length > 0 ? "~" + String.join("~", extension).toUpperCase() : "");
    }

    /**
     * The method responsible for returning
     * the login message which is to be
     * sent by the client to the server to
     * successfully log in to the server
     * following the protocol specified.
     * @param username - The client username
     * @return a String which contains the
     * login message to be sent according to the
     * protocol
     */
    public static String cLOGIN(String username) {
        return "LOGIN" + "~" + username;
    }

    /**
     * The method responsible for returning
     * the LIST message which is to be
     * sent by the client to the server to
     * request a list of online users.
     * @return a String which contains the
     * LIST message to be sent according to the
     * protocol
     */
    public static String cLIST() {
        return "LIST";
    }

    public static String cRANK() {
        return "RANK";
    }

    /**
     * The method responsible for returning
     * the QUEUE message which is to be
     * sent by the client to the server to
     * request get into a QUEUE to start
     * the Pentago game!
     * @return a String which contains the
     * QUEUE message to be sent according to the
     * protocol
     */
    public static String cQUEUE() {
        return "QUEUE";
    }

    /**
     * The method responsible for returning
     * the MOVE message which is to be
     * sent by the client to the server to
     * play a move in the pentago game!
     * @param index - the int value storing
     *              where the user wants to
     *              place the marble on the
     *              board.
     * @param rotate - the int value storing
     *               how the user want to rotate
     *               the Pentago board.
     * @return a String which contains the
     * MOVE message to be sent according to the
     * protocol
     */
    public static String cMOVE(int index, int rotate) {
        return "MOVE" + "~" + index + "~" + rotate;
    }

    /**
     * The method responsible for returning
     * the PING message which is to be
     * sent by the client to the server
     * to check active connection. The
     * server must immediately respond with
     * a PONG to indicate active connection to
     * the client.
     * @return a String which contains the
     * PING message to be sent according to the
     * protocol
     */
    public static String cPING() {
        return "PING";
    }

    /**
     * The method responsible for returning
     * the PONG message which is to be
     * sent by the client to the server
     * to check active connection. The client
     * sends this responding to a PING message
     * by the server
     * @return a String which contains the
     * PONG message to be sent according to the
     * protocol
     */
    public static String cPONG() {
        return "PONG";
    }

    /**
     * The method responsible for returning
     * the QUIT message which is to be
     * sent by the client to quit the connection
     * to the server.
     * @return a String which contains the
     * QUIT message to be sent according to the
     * protocol
     */
    public static String cQUIT() {
        return "QUIT";
    }
}
