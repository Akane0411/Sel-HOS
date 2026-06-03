module HOS.Proof.ProofH where

import HOS
import Control.Monad.Free ( Free(..) ) 

worker :: (Monoid r, Show r, Ord r) => Sel r VoidEff a -> r -> (a, r)
worker (HOS.Pure a) acc = (a, acc)
worker (Loss r k) acc = worker k (acc <> r)
worker (GetLoss k) acc = worker (k acc) acc
worker (Silence p k) acc =
    let (x, r) = worker p mempty
    in worker (k (x, r)) acc
worker (LReset k) acc = 
    fst $ worker (fmap (\p -> worker p acc) k) mempty
worker (Handler h p k) acc = do
    let p1 = handlerG h ((\x -> fmap snd $ silence (k x))) p
    worker (p1 >>= k) acc

runSelN :: Sel r e a -> (a, r)
runSelN = undefined

(===) :: a -> a -> a
x === y = y

proofLoss :: (Monoid r, Show r, Ord r) 
    => r -> Sel r VoidEff a -> r -> (a,r)
proofLoss r q acc = 
        worker ((loss r) >> q) acc
    === worker (Loss r q) acc

proofLreset :: (Monoid r, Show r, Ord r) 
    => Sel r VoidEff a -> (a -> Sel r VoidEff b) -> r -> (b,r)
proofLreset q k acc = 
        worker ((lreset q) >>= k) acc
    === worker (LReset (fmap k q)) acc
    === fst (worker (fmap (\t -> worker t acc) (fmap k q)) mempty)
    === fst (worker (fmap ((\t -> worker (k t) acc)) q ) mempty)
    === fst ((mempty <>) <$> runSelN (fmap ((\t -> worker (k t) acc)) q))
    === fst ((mempty <>) <$> runSelN (fmap (\t -> (acc <>) <$> runSelN (k t)) q))

proofHandler :: (Monoid r, Show r, Ord r, Functor e, Functor m) 
    => Handler r e VoidEff m -> Sel r (e :* VoidEff) a -> ((m a) -> Sel r VoidEff b) -> r -> (b,r)
proofHandler h q k acc =
        worker ((handler h q) >>= k) acc
    === worker (Handler h q k) acc
    === worker ((handlerG h (\x -> fmap snd $ silence (k x)) q) >>= k) acc

    -- === (acc <>) <$> (runSel $ handlerPRet h q >>= k)



proofHandlerOp :: (Monoid r, Show r, Ord r, Functor e, Functor m) 
    => Handler r e VoidEff m -> (e :* VoidEff) (Sel r (e :* VoidEff) a) -> (m a -> Sel r VoidEff b) -> r -> (b, r)
proofHandlerOp h op k acc =
        worker ((handler h (Op op)) >>= k) acc
    === worker (Handler h (Op op) k) acc
    === worker (handlerG h ((\x -> fmap snd $ silence (k x))) (Op op) >>= k) acc




proofHandlerLoss :: (Monoid r, Show r, Ord r, Functor e, Functor m) 
    => Handler r e VoidEff m -> r -> Sel r (e :* VoidEff) a -> ((m a) -> Sel r VoidEff b) -> r -> (b,r)
proofHandlerLoss h r q k acc =
        worker ((handler h (Loss r q)) >>= k) acc
    === worker (Handler h (Loss r q) k) acc
    === worker ((handlerG h (\x -> fmap snd $ silence (k x)) (Loss r q)) >>= k) acc
    === worker ((Loss r (handlerG h (\x -> fmap snd $ silence (k x)) q)) >>= k) acc
    === worker (Loss r (handlerG h (\x -> fmap snd $ silence (k x)) q >>= k)) acc
    === worker (handlerG h (\x -> fmap snd $ silence (k x)) q >>= k) (acc <> r)
    === worker (Handler h q k) (acc <> r)
    === worker (handler h q >>= k) (acc <> r)
    === worker (Loss r (handler h q >>= k)) r
    === worker (loss r >> (Handler h q k)) r

    -- IH   
    -- === ((acc <> r) <>) <$> (runSelN (handlerPRet h q) >>= k)

  
proofLemmaLOp :: (Monoid r, Show r, Ord r, Functor e, Functor es, Functor m) 
    => Handler r e es m -> (m a -> Sel r es r) -> e (Sel r (e :* es) b) -> (b -> Sel r (e :* es) a) -> Sel r es (m a)
proofLemmaLOp h cont op q = 
        handlerG h cont (Op (LeftEff op) >>= q)
    === handlerG h cont (Op $ fmap (>>= q) (LeftEff op))
    === handlerG h cont (Op $ LeftEff (fmap (>>= q) op))
    === (h_ops h) (fmap ( \p -> ( handlerG h cont p 
                                , toLossCont (handlerG h cont p) cont))                                         
                        (fmap (>>= q) op))
    === (h_ops h) (fmap ( \p -> ( handlerG h cont p 
                                , do
                                    (x, r1) <- silence (handlerG h cont p)
                                    r2 <- cont x
                                    return (r1 <> r2)) 
                        )                                         
                        (fmap (>>= q) op))




proofLemmaLoss :: (Monoid r, Show r, Ord r, Functor e, Functor es, Functor m) 
    => Handler r e es m -> (m a -> Sel r es r) -> r -> (Sel r (e :* es) a) -> Sel r es (m a)
proofLemmaLoss h cont r q = 
        handlerG h cont ( loss r >> q )
    === handlerG h cont (Loss r q)
    === Loss r (handlerG h cont q)
    === (loss r >> handlerG h cont q)
