-- Definitions about natural numbers and primes
import data.nat.prime

-- Library on linear arithmatic
import tactic.linarith

-- Define namespace, which is natural numbers in this case
open nat 


-- Define theorem or goal to prove
theorem infinitude_of_primes: ∀ N, ∃ p >= N, prime p :=
-- between begin-end block we write tactics
begin
  -- define N to be a natural number as a part of our local hypothesis
  intro N,

  -- Continue with proof as mentioned in link provided in header
  -- let M to be N! + 1
  let M := factorial N + 1,
  
  -- let p be smallest prime factor of M which is not 1
  let p := min_fac M,


  -- define supporting hypothesis pp, p is prime
  have pp : prime p := 
  -- begin proof for supporting p being prime
  begin
    -- minimum factor of a number is prime, but what about if M = 1
    refine min_fac_prime _,
    -- so here we prove M != 1 or M > 1
    have : factorial N > 0 := factorial_pos N,
    -- this just automatically takes care of linear arithmatic required for proof
    linarith,
  end,

  -- before this we had existenial statement but now we have condition in p
  use p,

  -- split our goal in  2 subgoals
  split,

  -- proof by contradiction so it should output False
  {by_contradiction,
   
   /- hypothesis h1, p divides N! + 1 proved by  
   min_fac_dvd : ∀ (n : ℕ), n.min_fac ∣ n
   -/
   have h₁ : p ∣ factorial N + 1 := min_fac_dvd M, 
   
   -- hypothesis h2, p divides N!
   have h₂ : p ∣  factorial N := 
   begin
     refine pp.dvd_factorial.mpr _,
     -- proved p <= N, using hypothsis h
     exact le_of_not_ge h,
   end,
   /-
   proved using dvd_add_right with support from local hypothesis h₂ and h₁
   -/
   have h : p ∣ 1 := (nat.dvd_add_right h₂).mp h₁,
   -- prime not dividing one using local hypothesis pp and h
   exact prime.not_dvd_one pp h, },
   -- second part of proof is just our hypothesis pp that we already proved
  {exact pp, },
end