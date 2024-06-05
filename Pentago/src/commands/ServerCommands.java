package commands;
/**
 * The class containing the Server commands
 * following the protocol specified to us
 * in the project description!
 * @author Kevin Schurman and Arsalaan Khan
 */
public class ServerCommands {

    /**
     * The method responsible for returning
     * the hello message which is to be
     * sent by the sever to the client.
     * @param description - The server description
     * @param extension - The extensions the server supports
     * @return a String which contains the
     * hello message to be sent according to the
     * protocol.
     */
    public static String sHELLO(String description, String... extension) {
        return "HELLO" + "~" + description
                + (extension.length > 0 ? "~" + String.join("~", extension).toUpperCase() : "");
    }

    /**
     * The method responsible for returning
     * the login message which is to be
     * sent by the server to the client
     * to confirm the login of a user!
     * following the protocol specified
     * @return a String which contains the
     * login message to be sent according to the
     * protocol.
     */
    public static String sLOGIN() {
        return "LOGIN";
    }

    /**
     * The method responsible for returning
     * the alreadyloggedin message which is to be
     * sent by the server to the client to indicate
     * that a user is already logged in.
     * @return a String which contains the
     * alreadyloggedin message to be sent
     * according to the protocol.
     */
    public static String sALREADYLOGGEDIN() {
        return "ALREADYLOGGEDIN";
    }

    /**
     * The method responsible for returning
     * the list message which is to be
     * sent by the server to the client to respond
     * to a list message sent by the client which
     * will contain the list of all connected clients!
     * @param individuals - A string containing all the
     *                    connected clients
     * @return a String which contains all the
     * connected clients sent according to the protocol
     * specified.
     */
    public static String sLIST(String... individuals) {
        return "LIST" + (individuals.length > 0 ? "~" + String.join("~", individuals) : "");
    }

    public static String sRANK(String... individuals) {
        return "RANK" + (individuals.length > 0 ? "~" + String.join("~", individuals) : "");
    }

    /**
     * The method responsible for returning
     * the list message which is to be
     * sent by the server to the client to indicate
     * the start of a new game once it has 2 players in the
     * queue waiting to play a game!
     * @param p1 - The name of player 1
     * @param p2 - The name of player 2
     * @return a String which tells the client about
     * the start of a new game following the protocol!
     */
    public static String sNEWGAME(String p1, String p2) {
        return "NEWGAME" + "~" + p1 + "~" + p2;
    }

    /**
     * The method responsible for returning
     * the list message which is to be
     * sent by the server to the client to indicate
     * the move played by the client!
     * @param index - The index on the board where the
     *              player decided to place a marble
     * @param rotate - The rotation chosen by the
     *               player
     * @return a String which tells the client about
     * the move played by the client following the protocol!
     */
    public static String sMOVE(int index, int rotate) {
        return "MOVE" + "~" + index + "~" + rotate;
    }

    /**
     * The method responsible for returning
     * the GAMEOVER message to be sent to the client in
     * the case of a game being over.
     * @param reason - The reason for the game being over
     * @param winner - The winner of the game in case there is one
     * @return a String containing the GAMEOVER message to be sent
     * to the client according to the protocol
     */
    public static String sGAMEOVER(String reason, String... winner) {
        return "GAMEOVER" + "~" + reason
                + (winner.length > 0 ? "~" + String.join("~", winner) : "");
    }

    /**
     * The method responsible for returning
     * the PING message which is to be
     * sent by the server to the client
     * to check active connection. The
     * client must immediately respond with
     * a PONG to indicate active connection to
     * the server.
     * @return a String which contains the
     * PING message to be sent according to the
     * protocol
     */
    public static String sPING() {
        return "PING";
    }

    /**
     * The method responsible for returning
     * the PONG message which is to be
     * sent by the server to the client
     * to check active connection. The server
     * sends this responding to a PING message
     * by the client
     * @return a String which contains the
     * PONG message to be sent according to the
     * protocol
     */
    public static String sPONG() {
        return "PONG";
    }

    /**
     * The method responsible for returning
     * the QUIT message which is to be
     * sent by the server to quit the connection
     * to the client.
     * @return a String which contains the
     * QUIT message to be sent according to the
     * protocol
     */
    public static String sQUIT() {
        return "QUIT";
    }

    /**
     * The method responsible for returning
     * the ERROR message to be sent to the client in
     * the case of an error.
     * @param description - The description of the error
     * @return a String containing the description of the game
     */
    public static String sERROR(String... description) {
        return "ERROR" + (description.length > 0 ? "~" + String.join("~", description) : "");
    }
}
