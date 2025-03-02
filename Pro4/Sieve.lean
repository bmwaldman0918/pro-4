
def setDiff (l l' : Stream Nat Nat) : Stream Nat Nat :=
  let x := stream.head l
  let xs := stream.tail l

  let y := stream.head l'
  let ys := stream.tail l'

  if x < y
    then stream.cons x (setDiff xs l')
  else if x == y
    then setDiff xs ys
  else -- if x > y
    setDiff l ys

def makeP (f : Nat) (l : Stream Nat Nat) : Stream Nat Nat :=
  2 :: (setDiff (stream f) l)

def makeC (l : List Nat) : List Nat :=

def eratosthenes (fuel : Nat) : List Nat :=
  match fuel with
  | Nat.zero => []
  | Nat.succ _ => [] -- change later
