package clientside;

import clientside.client.ClientMethod;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.io.PrintWriter;

/**
 * The class containing the main method
 * to run the client! Starts a thread of
 * clientMethod!
 * @author Kevin Schurman and Arsalaan Khan
 */
public class ClientSideMethod {
    /**
     * The main method that is executed at runtime!
     * @param args for arguments made from the client
     */
    public static void main(String[] args) {
        BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
        PrintWriter pw = new PrintWriter(System.out, true);
        new ClientMethod(br, pw, args).start();
    }
}
