package gamelogic.test;

import gamelogic.game.Game;
import gamelogic.game.GameMethod;
import gamelogic.player.*;

import org.junit.After;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.*;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;

/**
 * The test unit cases for the game method to see if the game and board classes works.
 * @author Kevin Schurman and Arsalaan Khan
 */
public class GameMethodTest implements Runnable {
    private Thread t;
    private Game game;
    private Player p1;
    private Player p2;

    private PipedReader pr1;
    private PipedWriter pw1;
    private PrintWriter pp1;

    private PipedReader pr2;
    private PipedWriter pw2;
    private PrintWriter pp2;

    private ReentrantLock lock;
    private Condition boardSignal;

    @BeforeEach
    public void setup() {
        try {
            pr1 = new PipedReader();
            pw1 = new PipedWriter(pr1);
            pp1 = new PrintWriter(pw1, true);

            pr2 = new PipedReader();
            pw2 = new PipedWriter(pr2);
            pp2 = new PrintWriter(pw2, true);

            PlayerFactory pf = new PlayerFactoryMethod();
            p1 = pf.makeHumanPlayer("Test Human Player 1", pr1, Mark.WHITE);
            p2 = pf.makeHumanPlayer("Test Human Player 2", pr2, Mark.BLACK);

            lock = new ReentrantLock();
            boardSignal = lock.newCondition();

            game = new GameMethod(p1, p2, lock, boardSignal);
            t = new Thread(this);
            t.start();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    /**
     * This method tests if placement of the
     * marbles on the game board is indeed
     * correct according to the user input.
     * The test passes if the field is what
     * the user set it to by inputting in the
     * console.
     * The test fails if the fields is not
     * what the user set it to by inputting
     * in the console
     *
     */
    @Test
    public void testPlacementAndRotation() {
        Assertions.assertSame(game.getBoard().getField(0), Mark.EMPTY);

        pp1.println("0 0");

        Assertions.assertSame(game.getBoard().getField(0), Mark.EMPTY);
        Assertions.assertNotSame(game.getBoard().getField(0), Mark.BLACK);
        Assertions.assertNotSame(game.getBoard().getField(0), Mark.WHITE);
        Assertions.assertSame(game.getBoard().getField(game.getBoard().index(2, 0)), Mark.EMPTY);
        Assertions.assertNotSame(game.getBoard().getField(game.getBoard().index(2, 0)), Mark.WHITE);

        pp1.println("0");
        lock.lock();
        try {
            boardSignal.await();
        } catch (InterruptedException e) {
            System.out.println("An error happened!");
        }
        lock.unlock();

        Assertions.assertNotSame(game.getBoard().getField(game.getBoard().index(2, 0)), Mark.EMPTY);
        Assertions.assertNotSame(game.getBoard().getField(0), Mark.WHITE);
        Assertions.assertSame(game.getBoard().getField(game.getBoard().index(2, 0)), Mark.WHITE);
    }

    /**
     * This method tests if the game
     * is indeed over when the game has a winner
     * or is a draw by passing in multiple inputs
     * continuously.
     * The test passes if the game is indeed
     * over after the continuous inputs.
     * The test fails if the game is not
     * over even after the game has a winner
     * or the board is full
     *
     */
    @Test
    public void testGameOver() {
        int row = 0, col = 0;
        while (!game.getBoard().gameOver()) {
            Assertions.assertFalse(game.getBoard().gameOver());
            while (p1 == game.getCurrent()) {
                while (!game.getBoard().isEmptyField(game.getBoard().index(row, col))) {
                    col++;
                    if (col >= (game.getBoard().getDim() * 2)) {
                        col = 0;
                        row++;
                        if (row >= (game.getBoard().getDim() * 2)) {
                            row = 0;
                        }
                    }
                }

                pp1.println(row + " " + col);
                pp1.println(6);

                lock.lock();
                try {
                    boardSignal.await();
                } catch (InterruptedException e) {
                    System.out.println("An error happened!");
                }
                lock.unlock();

                if (game.getBoard().gameOver()) {
                    break;
                }
                Assertions.assertFalse(game.getBoard().gameOver());
            }

            while (p2 == game.getCurrent()) {
                Assertions.assertFalse(game.getBoard().gameOver());
                while (!game.getBoard().isEmptyField(game.getBoard().index(row, col))) {
                    col++;
                    if (col >= (game.getBoard().getDim() * 2)) {
                        col = 0;
                        row++;
                        if (row >= (game.getBoard().getDim() * 2)) {
                            row = 0;
                        }
                    }
                }

                pp2.println(row + " " + col);
                pp2.println(6);

                lock.lock();
                try {
                    boardSignal.await();
                } catch (InterruptedException e) {
                    System.out.println("An error happened!");
                }
                lock.unlock();

                if (game.getBoard().gameOver()) {
                    break;
                }
                Assertions.assertFalse(game.getBoard().gameOver());
            }
        }
        System.out.println(game.update());
        System.out.println(game.result());
        Assertions.assertTrue(game.getBoard().gameOver());
    }

    /**
     * This method tests if there is indeed
     * a winner on the board and the winner is
     * correct. It is done by passing inputs
     * that will ensure the winning condition
     * of Mark.BLACK and then checks if Mark.BLACK
     * is indeed the winner
     * The test passes if the Mark.BLACK is the
     * winner after ensuring that it should
     * win
     * The test fails if Mark.BLACK is not
     * the winner or Mark.WHITE is the winner.
     *
     */
    @Test
    public void testWinner() {
        int row = 0, col = 0;
        while (!game.getBoard().gameOver()) {
            while (p1 == game.getCurrent()) {
                while (!game.getBoard().isEmptyField(game.getBoard().index(row, col))) {
                    col++;
                    if (col >= (game.getBoard().getDim() * 2)) {
                        col = 0;
                        row++;
                        if (row >= (game.getBoard().getDim() * 2)) {
                            row = 0;
                        }
                    }
                }

                pp1.println(row + " " + col);
                pp1.println(6);

                lock.lock();
                try {
                    boardSignal.await();
                } catch (InterruptedException e) {
                    System.out.println("An error happened!");
                }
                lock.unlock();

                if (game.getBoard().gameOver()) {
                    break;
                }
            }

            while (p2 == game.getCurrent()) {
                while (!game.getBoard().isEmptyField(game.getBoard().index(row, col))) {
                    col++;
                    if (col >= (game.getBoard().getDim() * 2)) {
                        col = 0;
                        row++;
                        if (row >= (game.getBoard().getDim() * 2)) {
                            row = 0;
                        }
                    }
                }

                pp2.println(row + " " + col);
                pp2.println(6);

                lock.lock();
                try {
                    boardSignal.await();
                } catch (InterruptedException e) {
                    System.out.println("An error happened!");
                }
                lock.unlock();

                if (game.getBoard().gameOver()) {
                    break;
                }
            }
        }
        System.out.println(game.update());
        System.out.println(game.result());
        Assertions.assertTrue(game.getBoard().isWinner(Mark.BLACK));
        Assertions.assertFalse(game.getBoard().isWinner(Mark.WHITE));
    }
    /**
     * This method tests if the game indeed
     * got over at the end after placing
     * random moves on the board by using the
     * hint functionality of the game which
     * returns a random legal move. A game
     * is over when it's a draw or has a winner.
     *
     * The test passes if game indeed gets over
     * after multiple random executions.
     * The test fails if game is not over even
     * after continuously sending input.
     *
     */
    @Test
    public void testRandom() {
        int row, col;
        while (!game.getBoard().gameOver()) {
            while (p1 == game.getCurrent()) {
                do {
                    Integer[] hint = game.getBoard().indexToRowCol(game.getBoard().getHint());
                    row = hint[0];
                    col = hint[1];
                } while (!game.getBoard().isEmptyField(game.getBoard().index(row, col)));

                pp1.println(row + " " + col);
                pp1.println((int) (Math.random() * 7));

                lock.lock();
                try {
                    boardSignal.await();
                } catch (InterruptedException e) {
                    System.out.println("An error happened!");
                }
                lock.unlock();

                if (game.getBoard().gameOver()) {
                    break;
                }
            }

            while (p2 == game.getCurrent()) {
                do {
                    Integer[] hint = game.getBoard().indexToRowCol(game.getBoard().getHint());
                    row = hint[0];
                    col = hint[1];
                } while (!game.getBoard().isEmptyField(game.getBoard().index(row, col)));

                pp2.println(row + " " + col);
                pp2.println((int) (Math.random() * 7));

                lock.lock();
                try {
                    boardSignal.await();
                } catch (InterruptedException e) {
                    System.out.println("An error happened!");
                }
                lock.unlock();

                if (game.getBoard().gameOver()) {
                    break;
                }
            }
        }
        System.out.println(game.update());
        System.out.println(game.result());
        Assertions.assertTrue(game.getBoard().gameOver());
    }

    /**
     * The method that will be called after every
     * test to make sure all the readers and writers
     * are closed!
     */
    @After
    public void end() {
        t.interrupt();

        try {
            pr1.close();
            pw1.close();
            pp1.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
        try {
            pr2.close();
            pw2.close();
            pp2.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    /**
     * Starting a new game!
     */
    @Override
    public void run() {
        game.startGame();
    }
}
