-----------------------------------------------------------------------------
{- |
Module      :  Language.Javascript.JMacro.Base
Copyright   :  (c) Gershom Bazerman, 2009
License     :  BSD 3 Clause
Maintainer  :  gershomb@gmail.com
Stability   :  experimental

Simple EDSL for lightweight (untyped) programmatic generation of Javascript.
-}
-----------------------------------------------------------------------------

module Language.Javascript.JMacro (
  module Language.Javascript.JMacro.Base,
  module Language.Javascript.JMacro.QQ
 ) where

import Prelude hiding (tail, init, head, last, minimum, maximum, foldr1, foldl1, (!!), read)

import Language.Javascript.JMacro.Base hiding (expr2stat)
import Language.Javascript.JMacro.QQ
