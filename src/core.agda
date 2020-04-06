{-# OPTIONS --prop #-}

module core where

--------------------------------------------------

postulate
  Ens : Set
  _∈_ : Ens → Ens → Prop

infix 0 _∈_

--------------------------------------------------
