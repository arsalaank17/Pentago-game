# Resit-6

This project contains a client-side, server-side, and direct ability to play of a Pentago game.

This is a collaborative assignment with Arsalaan Khan and Kevin Schurman.

## How to use

### Starting the Client

To use or play with the client, it is recommended that you are using a Linux environment since there is a lot more consistency and comfortability there than on Windows.

First build then run the client, specifically `ClientSideMethod` as that is the main method.

When running, you will be given some information before you can continue, which is to connect to the server and connect to their port number.

Once connected, you will need to log in and make sure it isn't a duplicated name already in the server (the client will tell you this once you have inputted your name).

If you are stuck or unable to figure out what to do with some specific things, write in the terminal: `HELP`.

Don't worry about case specifics when writing down words in the console, as long as the command is correct then you should receive the correct output from the input you have made.

If you wish to see further information of the client, such as exceptions being made, communication from the server (sending and receiving), in the program arguments, put in the flag `--debug`.

### Starting the Server

To use or play with the server, it is recommended that you are using a Linux environment since there is a lot more consistency and comfortability there than on Windows.

First build then run the client, specifically `ServerSideMethod` as that is the main method.

When running, you should then write down a port number that will be used when clients are connecting to your server and communicating with it to play games or other such.

The server will print all information that the user is inputting.

### Starting the Direct game

To use or play with the Game Logic package, build then run the GameLogicMain class, and you should be able to play the game and interact with the game.

You can also use `-N` for a Naive Computer or `-S` for a Smart Computer either in the arguments, or (if the argument count is not 2) directly in the game where it asks for it.

If neither `-N` or `-S` is used, the game will take in the input as a name.

## Test Cases

To run the test cases for the Board or Game of the Game Logic package, you should go to the test package and run the JUnit classes.