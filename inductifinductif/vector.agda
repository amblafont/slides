{-# OPTIONS  --rewriting  #-}

module vector where
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality 
{-# BUILTIN REWRITE _≡_ #-}


data Vector : ℕ → Set where
  []  : Vector zero
  _∷_ : {n : ℕ} → ℕ → Vector n → Vector (suc n)

plus-n-Sm : ∀ n m →   n + suc m ≡ suc (n + m)
plus-n-Sm = +-suc

{-# REWRITE plus-n-Sm  #-}


rev-append : (n : ℕ) → Vector n → (m : ℕ) → Vector m → Vector (n + m)
rev-append .0 [] m v2 = v2
-- rev-append .(suc _) (x ∷ v1) m v2 = rev-append _ v1 _ (x ∷ v2)
rev-append .(suc _) (x ∷ v1) m v2 =  rev-append _ v1 _ (x ∷ v2)  
