module Crypto where

import Data.Char

import Prelude hiding (gcd)

{- 
The advantage of symmetric encryption schemes like AES is that they are efficient 
and we can encrypt data of arbitrary size. The problem is how to share the key. 
The flaw of the RSA is that it is slow and we can only encrypt data of size lower 
than the RSA modulus n, usually around 1024 bits (64 bits for this exercise!).

We usually encrypt messages with a private encryption scheme like AES-256 with 
a symmetric key k. The key k of fixed size 256 bits for example is then exchanged 
via the aymmetric RSA. 
-}

-------------------------------------------------------------------------------
-- PART 1 : asymmetric encryption

-- Given two integers m and n, gcd recursively computes their
-- greatest common divisor
gcd :: Int -> Int -> Int
gcd m n 
  | n == 0    = m
  | otherwise = gcd n (m `mod` n) 

-- The phi function computes the eauler totient function for a given m
phi :: Int -> Int
--pre: m >= 0
phi m
  = length [x |  x <- [1 .. m], gcd x m == 1] 

--
-- Calculates (u, v, d) the gcd (d) and Bezout coefficients (u and v) 
-- such that au + bv = d
--
-- Pre: a,b >= o
extendedGCD :: Int -> Int -> ((Int, Int), Int)
extendedGCD a b
  | b == 0    = ((1,0),a) 
  | otherwise = ((v',(u' - q * v')), d)
    where
      (q, r)  = quotRem a b
      ((u', v'), d) = extendedGCD b r

-- Inverse of a modulo m
inverse :: Int -> Int -> Int
inverse a m
  | gcd a m == 1 = u `mod` m
  | otherwise = error "there is no inverse!"
    where
    ((u, _), _) = extendedGCD a m
  
-- Calculates (a^k mod m)
--
-- This function was a challenging one to come up with but eventually
-- managed it. first started off not doing it recursively due to 
-- the formulas given in the spec
-- this uses fermat's little theorem which is also used to proved RSA
-- correctness 
modPow :: Int -> Int -> Int -> Int
modPow a k m
  | k == 0    = 1 `mod` m
  | even k    = modPow amm j m
  | otherwise = a * (modPow amm j m) `mod` m
    where 
      j  = k `div` 2 
      amm = a * a `mod` m

-- Returns the smallest integer that is coprime with phi
--
-- Struggled for at least half an hour with this function as well
-- since i just couldn't get my head around it unntil I looked in
-- the course notes and realised i could use an accumulating 
-- parameter
smallestCoPrimeOf :: Int -> Int
smallestCoPrimeOf phi
  = smallestCoPrimeOf' 2
    where
      smallestCoPrimeOf' c
        | gcd c phi == 1 = c
        | otherwise      = smallestCoPrimeOf' (c + 1) 
  
-- Generates keys pairs (public, private) = ((e, n), (d, n))
-- given two "large" distinct primes, p and q
genKeys :: Int -> Int -> ((Int, Int), (Int, Int))
genKeys p q
  = ((e, p * q), (d, p * q))
    where
      e = smallestCoPrimeOf p'q'  
      d = inverse e p'q'
      p'q' = (p - 1) * (q - 1)
    

-- RSA encryption/decryption; (e, n) is the public key
rsaEncrypt :: Int -> (Int, Int) -> Int
rsaEncrypt m (e, n)
  = modPow m e n

rsaDecrypt :: Int -> (Int, Int) -> Int
rsaDecrypt c (d,n )
  = modPow c d n 


-------------------------------------------------------------------------------
-- PART 2 : symmetric encryption

-- Returns position of a letter in the alphabet
toInt :: Char -> Int
toInt a
  = ord a - ord 'a'

-- Returns the n^th letter
toChar :: Int -> Char
toChar n 
  = chr (n + ord 'a')

-- "adds" two letters
add :: Char -> Char -> Char
add a b 
  = toChar ((toInt a + toInt b) `mod` 26)

-- "substracts" two letters
substract :: Char -> Char -> Char
substract a b 
  = toChar ((toInt a - toInt b) `mod` 26)

-- the next functions present
-- 2 modes of operation for block ciphers : ECB and CBC
-- based on a symmetric encryption function e/d such as "add"

-- ecb (electronic codebook) with block size of a letter
--
ecbEncrypt :: Char -> String -> String
ecbEncrypt key m 
  = [ add x key | x <- m]

ecbDecrypt :: Char -> String -> String
ecbDecrypt key m 
  = [substract x key | x <- m]

-- cbc (cipherblock chaining) encryption with block size of a letter
-- initialisation vector iv is a letter
-- last argument is message m as a string
--
cbcEncrypt :: Char -> Char -> String -> String
cbcEncrypt key iv "" 
  = ""
cbcEncrypt key iv (x : xs)
  = y : cbcEncrypt key y xs 
    where 
      y = add key (add iv x)

cbcDecrypt :: Char -> Char -> String -> String
cbcDecrypt key iv ""
  = ""
cbcDecrypt key iv (x : xs)
  = y' : cbcDecrypt key x xs
    where
      y = substract x key
      y'= substract y iv
