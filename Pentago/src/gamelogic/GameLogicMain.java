package gamelogic;

import gamelogic.computer.StrategyFactory;
import gamelogic.computer.StrategyFactoryMethod;
import gamelogic.game.Game;
import gamelogic.game.GameMethod;

import gamelogic.player.*;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;

/**
 * The main class where the game will be run.
 * Allows the user to play the Pentago game by
 * asking the user for input and printing the board.
 * @author Kevin Schurman and Arsalaan Khan
 */
public class GameLogicMain {

    public static void main(String[] args) {
        BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
        PrintWriter pw = new PrintWriter(System.out, true);

        PlayerFactory playerFactory = new PlayerFactoryMethod();
        StrategyFactory strategyFactory = new StrategyFactoryMethod();
        Player[] players = new Player[2];
        Mark[] mark = {Mark.BLACK, Mark.WHITE};
        if (args.length == 2) {
            for (int i = 0; i < 2; i++) {
                if (args[i].equals("-N")) {
                    players[i] = playerFactory.makeComputerPlayer(
                            strategyFactory.makeNaiveStrategy(), mark[i]);
                } else if (args[i].equals("-S")) {
                    players[i] = playerFactory.makeComputerPlayer(
                            strategyFactory.makeSmartStrategy(), mark[i]);
                } else {
                    players[i] = playerFactory.makeHumanPlayer(
                            args[i], br, mark[i], pw);
                }
            }
        } else {
            for (int i = 0; i < 2; i++) {
                pw.printf("Enter in player " + (i + 1) + " name. "
                        + "You can use \"-N\" for a Naive Computer "
                        + "or \"-S\" for a Smart Computer: ");
                String str = "";
                do {
                    try {
                        str = br.readLine();
                    } catch (IOException e) {
                        e.printStackTrace();
                    }
                    if (str.equals("")) {
                        pw.printf("Please input a correct name: ");
                    }
                } while (str.equals(""));
                if (str.equals("-N")) {
                    players[i] = playerFactory.makeComputerPlayer(
                            strategyFactory.makeNaiveStrategy(), mark[i]);
                } else if (str.equals("-S")) {
                    players[i] = playerFactory.makeComputerPlayer(
                            strategyFactory.makeSmartStrategy(), mark[i]);
                } else {
                    players[i] = playerFactory.makeHumanPlayer(
                            str, br, mark[i], pw);
                }
            }
        }
        Game game = null;
        boolean found = false;
        for (Player player : players) {
            if (player instanceof HumanPlayer) {
                game = new GameMethod(players[0], players[1], pw);
                found = true;
                break;
            }
        }
        if (!found) {
            game = new GameMethod(players[0], players[1]);
        }
        game.startGame();
        pw.println(game.getBoard().toString());
        pw.println(game.result());
        try {
            br.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
        pw.close();
    }
}
