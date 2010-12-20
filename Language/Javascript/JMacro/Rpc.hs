{-# LANGUAGE QuasiQuotes, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances #-}

{- |
Module      :  Language.Javascript.JMacro.Rpc
Copyright   :  (c) Gershom Bazerman, 2010
License     :  BSD 3 Clause
Maintainer  :  gershomb@gmail.com
Stability   :  experimental

Allows for the creation of rpc server/client pairs from monomorphic functions.
The server portion
is a function from a json-encoded list of parameters to a json
response. A list of server functions are expected to be wrapped by a
dispatch function in the server framework of your choice.

The client
portion generated from a function of arity n is a function from a
string identifying a server or a subdirectory on a server to an arity
n function from javascript expressions (of type
'Language.Javascript.JMacro.Base.JExpr') to a single javascript
expression. This expression, when evaluated on the client side, will
call back to the provided server with json-serialized arguments and yield
the result (deserialized from json). This client function is expected to be embedded
via antiquotation into a larger block of jmacro code.

Client portions must unfortunately be given explicit type signatures.

The following example is a server/client pair providing an ajax call to add integers.

> testRPCCall :: String -> JExpr -> JExpr -> JExpr
> (testRPC, testRPCCall) = mkWebRPC "test" $ \x y -> asIO $ return (x + (y::Int))

This code uses a simple request/response type based on strings to be as agnostic as possible about choice of web service stack. It can be used as is, or used as a model for code which targets a particular web stack (Happstack, Snap, FastCGI, etc.).

The jQuery Javascript library is used to handle ajax requests, and hence pages which embed RPC calls must have the jQuery javascript library loaded.

-}

module Language.Javascript.JMacro.Rpc (
  -- * API
  mkWebRPC, asIO, Request, Response(..), WebRPCDesc,
  -- * Helper Classes
  CallWebRPC(..),ToWebRPC(..)
) where

import Prelude hiding (tail, init, head, last, minimum, maximum, foldr1, foldl1, (!!), read)


import Language.Javascript.JMacro.Base
import Language.Javascript.JMacro.QQ

import Text.JSON
import Text.JSON.String

type WebRPCDesc = (String, Request -> IO Response)

-- | A String containing a json representation of function arguments encoded as a list of parameters. Generally would be passed as part of an HTTP request.
type Request = String

-- | Either a success or failure (with code). Generally would be turned back into a proper HTTP response.
data Response = GoodResponse String
              | BadResponse Int String

returnResp :: JSON a => a -> IO Response
returnResp r = return $ GoodResponse (encode r)
respCode c e = BadResponse c e
badData e = return $ respCode 400 ("Bad Data format: " ++ e)

class ToWebRPC a where
    toWebRPC_ :: a -> ([JSValue] -> IO Response)

instance (JSON b) => ToWebRPC (IO b) where
    toWebRPC_ f _ =  returnResp =<< f

instance (JSON a, ToWebRPC b) => ToWebRPC (a -> b) where
    toWebRPC_ f (x:xs) = case readJSON x of
                           Ok v -> toWebRPC_ (f v) xs
                           Error s -> badData s
    toWebRPC_ _ _ = badData "missing parameter"

toWebRPC :: ToWebRPC a => a -> Request -> IO Response
toWebRPC f = \req -> case runGetJSON readJSArray req of
                       (Right (JSArray xs)) ->f' xs
                       (Left e) -> badData e
                       _ -> badData "toWebRPC error"
    where f' = toWebRPC_ f

class CallWebRPC a b | a -> b where
    callWebRPC_ :: [JExpr] -> String -> a -> b

instance CallWebRPC (IO b) JExpr where
    callWebRPC_ xs serverLoc _ =
        [$jmacroE|
         (\() { var res;
//                $.post(`(serverLoc)`, { args : JSON.stringify `(reverse xs)` }, \(d) {res = d}, "json");
                $.ajax({type    : "POST",
                        url     : `(serverLoc)`,
                        data    : { args : JSON.stringify `(reverse xs)` },
                        success : \d {res = d},
                        dataType: "json",
                        async   : false
                      });
                return res;
               }())|]

instance (CallWebRPC b c, ToJExpr d) => CallWebRPC (a -> b) (d -> c) where
    callWebRPC_ xs serverLoc f = \x -> callWebRPC_ (toJExpr x : xs) serverLoc (f undefined)

callWebRPC :: (CallWebRPC a b) => String -> a -> b
callWebRPC s f = callWebRPC_ [] s f

-- | Produce a pair of (ServerFunction, ClientFunction) from a function in IO
mkWebRPC :: (ToWebRPC a, CallWebRPC a b) => String -> a -> (WebRPCDesc, String -> b)
mkWebRPC name rpcFun = ((name,toWebRPC rpcFun), \server -> callWebRPC (server ++ "/" ++ name) rpcFun)


testRPCCall :: String -> JExpr -> JExpr -> JExpr
(testRPC, testRPCCall) = mkWebRPC "test" $ \x y -> asIO $ return (x + (y::Int))

-- | id with a helpful type.
asIO :: IO a -> IO a
asIO = id
