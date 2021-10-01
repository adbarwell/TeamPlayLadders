module Main
import System.File
import public Examples

main : IO ()
main = do myFile <- openFile "eclipse_output" WriteTruncate
          case myFile of
              Right c => case generateAndPrint 10 of 
                            Just str => do fPutStr c str
                                           closeFile c
                            Err err => printLn err
                                            
              Left err => printLn err