a = \(x :: Y) (z :: W) -> x
b = \(x :: B -> C -> D -> A) (y :: B) (z :: C) (r :: E -> D) (s :: forall n. n) ->
  x y z (r (s @E))
c = (\(x :: a) -> \(y :: b) -> ((\(x :: a) -> x) :: forall a. _) @b) :: forall a b. _
d = (\(x :: i) -> with x (implicit @i (_ :: i))) :: forall i. _
e = (\(x :: forall a. a ~> a -> (a ~> a) -> a ~> a) -> x)
f = implicit @(I ~> i -> i) (implicit @I (_ :: i -> i)) :: forall i. _
