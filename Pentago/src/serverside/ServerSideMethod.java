package serverside;


import serverside.server.ServerMethod;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.ServerSocket;

/**
 * The class containing the main method
 * to start the server!
 * @author Kevin Schurman and Arsalaan Khan.
 */
public class ServerSideMethod {
    /**
     * The method used to start the server on the
     * inputted port!
     * @param args an array of sequence of characters
     *             (Strings) that are passed to this
     *             function when a program is executed.
     */
    public static void main(String[] args) {
        BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
        ServerSocket ss = null;
        System.out.print("Please input a port number from 0 to 65535 (or leave blank for 55555): ");
        do {
            try {
                String str = br.readLine();
                int port;
                if (str.equals("")) {
                    port = 55555;
                } else {
                    port = Integer.parseInt(str);
                }
                if (port >= 0 && port <= 65535) {
                    ss = new ServerSocket(port);
                }
            } catch (IOException | NumberFormatException e) {
//                e.printStackTrace();
                System.out.println("Please input a correct or valid port.");
            }
        } while (ss == null);
        System.out.println("Started Server!");
        new ServerMethod(ss).start();
    }
}
