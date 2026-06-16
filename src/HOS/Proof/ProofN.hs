{-# OPTIONS_GHC -Wno-noncanonical-monad-instances #-}

{-# LANGUAGE TypeOperators #-} 
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module HOS.Proof.ProofN where

import SelN
     
import Control.Monad( ap, liftM )
import Control.Monad.Free ( Free(..) ) 
import Control.Monad.Trans.Writer.Lazy ( censor, pass, WriterT(..), tell, runWriterT ) 
import Control.Monad.Trans.Class ( MonadTrans(lift) )




runSelN :: Monoid r => Sel r VoidEff a -> (a, r)
runSelN = runSel

pureN :: (Monoid r, Functor e) => a -> Sel r e a
pureN = pure

pureW :: (Monoid r, Functor e) => a -> WriterT r (Eff e) a
pureW = pure

pureE :: (Functor e) => a -> Eff e a
pureE = pure

(===) :: a -> a -> a
x === y = y


infixr 0 ===


fmap_G :: (a -> b) -> (a, r) -> (b, r)
fmap_G f (a,r) = (f a, r)


proofLreset :: (Monoid r, Show r, Ord r)
    => Sel r VoidEff a -> (a -> Sel r VoidEff b) -> r -> (b,r)
proofLreset q k acc =

        fst ((mempty <>) <$> runSelN (fmap (\t -> (acc <>) <$> runSelN (k t)) q))
    
    -- mempty
    === fst (runSelN (fmap (\t -> (acc <>) <$> runSelN (k t)) q))

    -- f . fmap_F g  = fmap_G g . f (naturality)
    === fst (fmap_G (\t -> (acc <>) <$> runSelN (k t)) (runSelN q))

    -- fst . fmap_G g  = g . fst (naturality)
    === (\t -> (acc <>) <$> runSelN (k t)) (fst (runSelN q))

    -- \t -> p(t) . fst = \t -> p (fst t)
    === (\(a,r) -> (acc <>) <$> runSelN (k a)) (runSelN q)

    -- def of fmap
    === (acc <>) <$> ((\(a,r) -> runSelN (k a)) (runSelN q))


    -- def of runSelN
    === (acc <>) <$> ((\(a,r) -> runSelN(k a))
            (case runWriterT (unSel q (\_ -> pureW mempty)) of
                Pure (a,r) -> (a,r)))

    -- distributivity of function over case 
    === (acc <>) <$> 
            case runWriterT (unSel q (\_ -> pureW mempty)) of
                Pure (a,r) -> (\(a,r) -> runSelN(k a)) (a,r)

    -- abstraction
    === (acc <>) <$> 
            case runWriterT (unSel q (\_ -> pureW mempty)) of
                Pure (a,_) -> runSelN(k a)
    
    -- def of runSel
    === (acc <>) <$> 
            case runWriterT (unSel q (\_ -> pureW mempty)) of
                Pure (a,_) -> 
                    case runWriterT (unSel (k a) (\_ -> pureW mempty)) of
                        Pure (a,r) -> (a, r)
    
    -- case-pureE lemma
    === (acc <>) <$> 
            let va = runWriterT (unSel q (\_ -> pureW mempty))     >>= \(a,_) ->
                    runWriterT (unSel (k a) (\_ -> pureW mempty))
            in case va of
                Pure (a,r) -> (a, r)

    -- distributivity of function over case
    === (acc <>) <$> 
            let va = runWriterT (unSel q (\_ -> pureW mempty))     >>= \(a,_) ->
                     runWriterT (unSel (k a) (\_ -> pureW mempty))
            in case va of
                    Pure (a,r) -> ((a,r))

    -- monad law 
    === (acc <>) <$> 
            let va = runWriterT (unSel q (\_ -> pureW mempty))  >>= \(a,w) ->
                     runWriterT (unSel (k a) (\_ -> pureW mempty)) >>= \(y, r2) ->
                     pureE (y, r2) 
            in case va of
                    Pure (a,r) -> (a,r)

    -- monad law 
    === (acc <>) <$> 
            let va = (
                        runWriterT (unSel q (\_ -> pureW mempty))  >>= \(a,w) ->
                        pureE (a, (const mempty) w)
                     )                                             >>= \(x, r1) ->
                     runWriterT (unSel (k x) (\_ -> pureW mempty)) >>= \(y, r2) ->
                     pureE (y, r1 <> r2 ) 
            in case va of
                    Pure (a,r) -> (a,r)

    -- monad law 
    === (acc <>) <$> 
            let va = (
                        runWriterT (unSel q (\_ -> pureW mempty))  >>= \(a,w) ->
                        pureE ((a,(const mempty)), w) >>= \((a, f), w) -> 
                        pureE (a, f w)
                     )                                              >>= \(x, r1) ->
                     runWriterT (unSel (k x) (\_ -> pureW mempty)) >>= \(y, r2) ->
                     pureE (y, r1 <> r2 ) 
            in case va of
                    Pure (a,r) -> (a,r)

    -- p >>= pure . f = fmap f p
    === (acc <>) <$> 
            let fn = fmap (\(a,w) -> ((a,(const mempty)), w)) . runWriterT
                va = ( 
                        fn (unSel q (\_ -> pureW mempty)) >>= \((a, f), w) -> 
                        pureE (a, f w)
                     )                                             >>= \(x, r1) ->
                     runWriterT (unSel (k x) (\_ -> pureW mempty)) >>= \(y, r2) ->
                     pureE (y, r1 <> r2 ) 
            in case va of
                    Pure (a,r) -> (a,r)

    --  fmap (\(a,w) -> (f a, w)) . runWriterT = runWriterT . fmap f
    === (acc <>) <$> 
            let fn = runWriterT . fmap (\x -> (x,(const mempty)))
                va = (
                        fn (unSel q (\_ -> pureW mempty)) >>= \((a, f), w) -> 
                        pureE (a, f w)
                     )                                             >>= \(x, r1) ->
                     runWriterT (unSel (k x) (\_ -> pureW mempty)) >>= \(y, r2) ->
                     pureE (y, r1 <> r2 ) 
            in case va of
                    Pure (a,r) -> (a,r)

    -- runWriter . WriterT
    === (acc <>) <$> 
            let fn = runWriterT . fmap (\x -> (x,(const mempty)))
                va = runWriterT (WriterT (
                        fn (unSel q (\_ -> pureW mempty)) >>= \((a, f), w) -> 
                        pureE (a, f w)
                     ))                                            >>= \(x, r1) ->
                     runWriterT (unSel (k x) (\_ -> pureW mempty)) >>= \(y, r2) ->
                     pureE (y, r1 <> r2 ) 
            in case va of
                    Pure (a,r) -> (a,r)

    -- def of pass 
    === (acc <>) <$> 
            let tt = pass (fmap (\x -> (x,(const mempty))) (unSel q (\_ -> pureW mempty)))
                va = runWriterT tt                                 >>= \(x, r1) ->
                     runWriterT (unSel (k x) (\_ -> pureW mempty)) >>= \(y, r2) ->
                     pureE (y, r1 <> r2 )
            in case va of
                Pure (a,r) -> (a,r)

    -- def of censor 
    === (acc <>) <$> 
            let tt = censor (const mempty) (unSel q (\_ -> pureW mempty))
                va = runWriterT tt                                 >>= \(x, r1) ->
                     runWriterT (unSel (k x) (\_ -> pureW mempty)) >>= \(y, r2) ->
                     pureE (y, r1 <> r2 ) 
            in case va of
                    Pure (a,r) -> (a,r)

    -- runWriterT . WriterT = id
    === (acc <>) <$> 
            let tt = censor (const mempty) (unSel q (\_ -> pureW mempty))
                va = runWriterT (WriterT ( 
                        runWriterT tt                                 >>= \(x, r1) ->
                        runWriterT (unSel (k x) (\_ -> pureW mempty)) >>= \(y, r2) ->
                        pureE (y, r1 <> r2 ) 
                     ))
            in case va of
                Pure (a,r) -> (a,r)

    -- abstraction
    === (acc <>) <$> 
            let tt = censor (const mempty) (unSel q (\_ -> pureW mempty))
                va = runWriterT ((\p -> WriterT ( 
                                    runWriterT tt              >>= \(x, r1) ->
                                    runWriterT (unSel (k x) p) >>= \(y, r2) ->
                                    pureE (y, r1 <> r2 ))
                                 ) (\_ -> pureW mempty))
            in case va of
                Pure (a,r) -> (a,r) -- pureE

    -- def of runSelN
    === (acc <>) <$> 
            let tt = censor (const mempty) (unSel q (\_ -> pureW mempty))
            in runSelN (
                Sel $ \p -> WriterT ( 
                    runWriterT tt              >>= \(x, r1) ->
                    runWriterT (unSel (k x) p) >>= \(y, r2) ->
                    pureE (y, r1 <> r2 ) ) 
                )

    -- def of >>= of WriterT
    === (acc <>) <$> 
            let tt = censor (const mempty) (unSel q (\_ -> pureW mempty))
            in runSelN ( Sel $ ( \p -> tt >>= \x -> unSel (k x) p) )

    -- abstraction
    === (acc <>) <$> 
            let tt = censor (const mempty) (unSel q (\_ -> pureW mempty))
            in runSelN (
                Sel $ (\p -> (\_ -> tt) (\a -> unSel (k a) p
                                            >>= \y -> p y)
                                            >>= \x -> unSel (k x) p)
                )

    -- def of >>= of SelN
    === (acc <>) <$> 
            let tt = censor (const mempty) (unSel q (\_ -> pureW mempty))
            in runSelN ((Sel { unSel = (\ _ -> tt) }) >>= k)

    -- def of runSelN
    === (acc <>) <$> runSelN ((lreset q) >>= k)



proofHandler' :: (Monoid r, Show r, Ord r, Functor e) 
    => Handler r e VoidEff a ans -> r -> Sel r (e :* VoidEff) a -> (ans -> Sel r VoidEff b) -> r -> (b,r)
proofHandler' h r q k acc = 
 --     worker ((handler h (Loss r q)) >>= k) acc
 --      :
 -- === worker (Handler h q k) (acc <> r)
    -- IH   
        ((acc <> r) <>) <$> (runSelN ((handlerPRet h q) >>= k))
    === (acc <>) <$> ((r <>) <$> (runSelN ((handlerPRet h q) >>= k)))

    -- === (acc <>) <$> ((r <>) <$> 
    --         let Sel sl = ((handlerPRet h q) >>= k) 
    --             va = runWriterT (sl (\a -> pure mempty))
    --         in case va of
    --             Pure (a,r2) -> (a, r2)
    --         )

    -- === (acc <>) <$> ( 
    --         let Sel sl = ((handlerPRet h q) >>= k) 
    --             va = runWriterT (sl (\a -> pure mempty))
    --         in case va of
    --             Pure (a,r2) -> (a, r <> r2)
    --         )

    -- === (acc <>) <$> runSelN (Sel { unSel = (\gamma -> 
    --                                     foldAlg 
    --                                         (sel2writer_ret (h_ret h) gamma) 
    --                                         (sel2writer_ops (h_ops h) gamma)
    --                                         (do
    --                                             sel2free q (h_ret h) gamma
    --                                             >>= \(b,r2) -> return (b, r <> r2)
    --                                         )  
    --                                 )} >>= k)



    === (acc <>) <$> runSelN (loss r >> (handlerPRet h q) >>= k)

    === (acc <>) <$> runSelN ((handlerPRet h (loss r >> q)) >>= k)













-- 主定理の Handler case の補題 (pure x)
proofLemmaPure :: (Monoid r, Show r, Ord r, Functor e, Functor es) 
    => Handler r e es a ans -> a -> Sel r es ans
proofLemmaPure h x = 

        handlerPRet h (pureN x)

    -- def ofhandllerPRet
    === Sel { unSel = 
                (\gamma -> 
                    foldAlg 
                        (sel2writer_ret (h_ret h) gamma) 
                        (sel2writer_ops (h_ops h) gamma)
                        (sel2free (pureN x) (h_ret h) gamma)
                )}

    -- def of sel2free
    === Sel { unSel = 
                (\gamma -> 
                    foldAlg 
                        (sel2writer_ret (h_ret h) gamma) 
                        (sel2writer_ops (h_ops h) gamma)
                        (runWriterT (unSel (pureN x) (\x -> 
                            writerTMap cast ((unSel ((h_ret h) x) gamma) >>= gamma)
                        )))
                )}

    -- def of pure of SelN
    === Sel { unSel = 
                (\gamma -> 
                    foldAlg 
                        (sel2writer_ret (h_ret h) gamma) 
                        (sel2writer_ops (h_ops h) gamma)
                        (runWriterT (unSel (Sel $ (\_ -> pureW x)) (\x -> 
                            writerTMap cast ((unSel ((h_ret h) x) gamma) >>= gamma)
                        )))
                )}

    -- unSel . Sel / fun app
    === Sel { unSel = 
                (\gamma -> 
                    foldAlg 
                        (sel2writer_ret (h_ret h) gamma) 
                        (sel2writer_ops (h_ops h) gamma)
                        (runWriterT ( pureW x ))
                )}

    -- runWriterT (pureW x) = pureE (x, mempty)
    === Sel { unSel = 
                (\gamma -> 
                    foldAlg 
                        (sel2writer_ret (h_ret h) gamma) 
                        (sel2writer_ops (h_ops h) gamma)
                        (pureE (x, mempty))
                )}

    -- runWriterT (pureW x) = pureE (x, mempty)
    === Sel { unSel = \gamma -> (sel2writer_ret (h_ret h) gamma) (x, mempty) }

    -- def of sel2writer_ret
    === Sel { unSel = \gamma -> (\(a, r) -> tell r >> unSel ((h_ret h) a) gamma) ((x, mempty)) }

    -- function application
    === Sel { unSel = \gamma -> tell mempty >> unSel ((h_ret h) x) gamma }

    -- def of tell
    === Sel { unSel = \gamma -> (unSel ((h_ret h) x) gamma) }

    -- eta-expansion
    === Sel { unSel = (unSel ((h_ret h) x)) }

    -- Sel . unSel = id
    === (h_ret h) x





-- 主定理の Handler case の補題 (Op op)
proofLemmaOp :: (Monoid r, Show r, Ord r, Functor e, Functor es) 
    => Handler r e es a ans -> e (Free (e :* es) b) -> (b -> Sel r (e :* es) a) -> Sel r es ans
proofLemmaOp h op q = 

        handlerPRet h ( Sel { unSel = \_ -> lift (Free (LeftEff op)) } >>= q )

    -- def of handlerPRet
    === Sel { unSel = (\gamma -> 
                foldAlg 
                    (sel2writer_ret (h_ret h) gamma) 
                    (sel2writer_ops (h_ops h) gamma)
                    (sel2free (Sel { unSel = \_ -> lift (Free (LeftEff op)) } >>= q) (h_ret h) gamma)
            )}
    
    -- def of sel2free
    === Sel { unSel = (\gamma -> 
                foldAlg 
                    (sel2writer_ret (h_ret h) gamma) 
                    (sel2writer_ops (h_ops h) gamma)
                    (runWriterT (unSel (Sel { unSel = \_ -> lift (Free (LeftEff op)) } >>= q) (\x -> 
                            writerTMap cast ((unSel ((h_ret h) x) gamma) >>= gamma)
                        )))
            )}

    -- def of >>= of SelN
    === Sel { unSel = (\gamma -> 
                foldAlg 
                    (sel2writer_ret (h_ret h) gamma) 
                    (sel2writer_ops (h_ops h) gamma)
                    (runWriterT (unSel (Sel { unSel = \p -> (\_ -> lift (Free (LeftEff op))) (\a -> unSel (q a) p >>= \y -> p y) >>= \x -> unSel (q x) p } ) (\x -> 
                            writerTMap cast ((unSel ((h_ret h) x) gamma) >>= gamma)
                        )))
            )}

    -- fun app
    === Sel { unSel = (\gamma -> 
                foldAlg 
                    (sel2writer_ret (h_ret h) gamma) 
                    (sel2writer_ops (h_ops h) gamma)
                    (runWriterT (unSel (Sel { unSel = \p -> lift (Free (LeftEff op)) >>= \x -> unSel (q x) p } ) (\x -> 
                            writerTMap cast ((unSel ((h_ret h) x) gamma) >>= gamma)
                        )))
            )}

    -- def of >>= of WriterT
    === Sel { unSel = (\gamma -> 
                foldAlg 
                    (sel2writer_ret (h_ret h) gamma) 
                    (sel2writer_ops (h_ops h) gamma)
                    (runWriterT (unSel (Sel { unSel = \p -> WriterT $ do
                        (a, r1) <- runWriterT $ lift (Free (LeftEff op))
                        (b, r2) <- runWriterT $ unSel (q a) p
                        return (b, r1 <>r2) } ) (\x -> 
                            writerTMap cast ((unSel ((h_ret h) x) gamma) >>= gamma)
                        )))
            )}

    -- def of lift 
    === Sel { unSel = (\gamma -> 
                foldAlg 
                    (sel2writer_ret (h_ret h) gamma) 
                    (sel2writer_ops (h_ops h) gamma)
                    (runWriterT (unSel (Sel { unSel = \p -> WriterT $ do
                        (a, r1) <- runWriterT $ WriterT $ do
                            a <- (Free (LeftEff op))
                            return (a, mempty)
                        (b, r2) <- runWriterT $ unSel (q a) p
                        return (b, r1 <>r2) } ) (\x -> 
                            writerTMap cast ((unSel ((h_ret h) x) gamma) >>= gamma)
                        )))
            )}

    -- 
    === Sel { unSel = (\gamma -> 
                foldAlg 
                    (sel2writer_ret (h_ret h) gamma) 
                    (sel2writer_ops (h_ops h) gamma)
                    (runWriterT (unSel (Sel { unSel = \p -> WriterT $ do
                        (a    ) <- (Free (LeftEff op))
                        (b, r2) <- runWriterT $ unSel (q a) p
                        return (b, r2) } ) (\x -> 
                            writerTMap cast ((unSel ((h_ret h) x) gamma) >>= gamma)
                        )))
            )}            

    -- p >>= return = p
    === Sel { unSel = (\gamma -> 
                foldAlg 
                    (sel2writer_ret (h_ret h) gamma) 
                    (sel2writer_ops (h_ops h) gamma)
                    (runWriterT (unSel (Sel { unSel = \p -> WriterT $ do
                        a <- (Free (LeftEff op))
                        runWriterT $ unSel (q a) p} ) (\x -> 
                            writerTMap cast ((unSel ((h_ret h) x) gamma) >>= gamma)
                        )))
            )}    

    -- unSel . Sel = id
    === Sel { unSel = (\gamma -> 
                foldAlg 
                    (sel2writer_ret (h_ret h) gamma) 
                    (sel2writer_ops (h_ops h) gamma)
                    (runWriterT (WriterT $ do
                        a <- (Free (LeftEff op))
                        runWriterT $ unSel (q a) (\x -> writerTMap cast ((unSel ((h_ret h) x) gamma) >>= gamma)))
                    )
            )}    
    
    -- runWriterT . WriterT = id / do -> >>=
    === Sel { unSel = (\gamma -> 
                foldAlg 
                    (sel2writer_ret (h_ret h) gamma) 
                    (sel2writer_ops (h_ops h) gamma)
                    (Free (LeftEff op) >>= \a -> 
                        runWriterT $ unSel (q a) (\x -> writerTMap cast ((unSel ((h_ret h) x) gamma) >>= gamma)))
            )}

    -- def of >>= of Free ( Free m >>= q = Free (fmap (>>= q) m) )
    === Sel { unSel = (\gamma -> 
                foldAlg 
                    (sel2writer_ret (h_ret h) gamma) 
                    (sel2writer_ops (h_ops h) gamma)
                    (Free $ fmap (>>= \a -> runWriterT $ unSel (q a) (\x -> writerTMap cast ((unSel ((h_ret h) x) gamma) >>= gamma))) (LeftEff op))
            )}

    -- def of sel2free
    === Sel { unSel = (\gamma -> 
                foldAlg 
                    (sel2writer_ret (h_ret h) gamma) 
                    (sel2writer_ops (h_ops h) gamma)
                    (Free $ fmap (>>= \a -> sel2free (q a) (h_ret h) gamma) (LeftEff op))
            )}

    -- def of foldAlg
    === Sel { unSel = (\gamma -> 
                (sel2writer_ops (h_ops h) gamma) 
                (fmap (foldAlg (sel2writer_ret (h_ret h) gamma) (sel2writer_ops (h_ops h) gamma)) 
                      (fmap (>>= \a -> sel2free (q a) (h_ret h) gamma) 
                            (LeftEff op)
                      )
                )
            )}
    
    -- fmap f (fmap g p) = fmap (f . g) p
    === Sel { unSel = (\gamma -> 
                (sel2writer_ops (h_ops h) gamma) 
                (fmap 
                    ((foldAlg (sel2writer_ret (h_ret h) gamma) (sel2writer_ops (h_ops h) gamma)) 
                        . (>>= \a -> sel2free (q a) (h_ret h) gamma) ) 
                    (LeftEff op)
                      
                )
            )}
    
    -- def of fmap of LeftEff
    === Sel { unSel = (\gamma -> 
                (sel2writer_ops (h_ops h) gamma) 
                ((LeftEff $ 
                    fmap 
                    ((foldAlg (sel2writer_ret (h_ret h) gamma) (sel2writer_ops (h_ops h) gamma)) 
                        . (>>= \a -> sel2free (q a) (h_ret h) gamma)) 
                    op
                ))
            )}

    -- def of sel2writer_ops
    === Sel { unSel = (\gamma -> 
                ((\hw -> unSel ((h_ops h) (fmap (\w -> 
                    ( Sel { unSel = \_ -> w},
                      Sel { unSel = \_ -> lift (fmap snd (runWriterT (w >>= gamma)))} )
                                    ) hw)) gamma) 
                            <+> blg) 
                ((LeftEff $ 
                    fmap 
                    ((foldAlg (sel2writer_ret (h_ret h) gamma) (sel2writer_ops (h_ops h) gamma)) 
                        . (>>= \a -> sel2free (q a) (h_ret h) gamma)) 
                    op
                ))
            )}
    
    -- def of <+>
    === Sel { unSel = (\gamma -> 
                (\hw -> unSel ((h_ops h) (fmap (\w -> 
                    ( Sel { unSel = \_ -> w},
                      Sel { unSel = \_ -> lift (fmap snd (runWriterT (w >>= gamma)))} )
                                    ) hw)) gamma)  
                ((fmap 
                    ((foldAlg (sel2writer_ret (h_ret h) gamma) (sel2writer_ops (h_ops h) gamma)) 
                        . (>>= \a -> sel2free (q a) (h_ret h) gamma)) 
                    op
                ))
            )}

    -- fun app
    === Sel { unSel = (\gamma -> 
                unSel ((h_ops h) (fmap (\w -> 
                        ( Sel { unSel = \_ -> w},
                          Sel { unSel = \_ -> lift (fmap snd (runWriterT (w >>= gamma)))} 
                        )) 
                        (fmap 
                            ((foldAlg (sel2writer_ret (h_ret h) gamma) (sel2writer_ops (h_ops h) gamma)) 
                                . (>>= \a -> sel2free (q a) (h_ret h) gamma)) 
                            op
                        )
                )) gamma 
            )}

    -- eta-expansion
    === Sel { unSel = (\gamma -> 
                (unSel ((h_ops h) (fmap (\w -> 
                        ( Sel { unSel = \_ -> w},
                          Sel { unSel = \_ -> lift (fmap snd (runWriterT (w >>= gamma)))} 
                        )) 
                        (fmap 
                            ((\freePgm -> foldAlg (sel2writer_ret (h_ret h) gamma) (sel2writer_ops (h_ops h) gamma) freePgm) 
                                . (\fa -> (>>= \a -> sel2free (q a) (h_ret h) gamma) fa)) 
                            op
                        )
                )) gamma)   
            )}

    -- (\x. f x) . (\y. g y) = \y. f (g y)
    === Sel { unSel = (\gamma -> 
                (unSel ((h_ops h) (fmap (\w -> 
                        ( Sel { unSel = \_ -> w},
                          Sel { unSel = \_ -> lift (fmap snd (runWriterT (w >>= gamma)))} 
                        )) 
                        (fmap 
                            (\fa -> foldAlg 
                                    (sel2writer_ret (h_ret h) gamma) 
                                    (sel2writer_ops (h_ops h) gamma) 
                                    (fa >>= \a -> sel2free (q a) (h_ret h) gamma)
                            ) op
                        )
                )) gamma)   
            )}

    -- def of lift
    === Sel { unSel = (\gamma -> 
                (unSel ((h_ops h) (fmap (\w -> 
                        ( Sel { unSel = \_ -> w},
                          Sel { unSel = \_ -> WriterT $ do
                                                a <- (fmap snd (runWriterT (w >>= gamma)))
                                                return (a, mempty)} 
                        )) 
                        (fmap 
                            (\fa -> foldAlg 
                                    (sel2writer_ret (h_ret h) gamma) 
                                    (sel2writer_ops (h_ops h) gamma) 
                                    (fa >>= \a -> sel2free (q a) (h_ret h) gamma)
                            ) op
                        )
                )) gamma)   
            )}

    === Sel { unSel = (\gamma -> 
                (unSel ((h_ops h) (fmap (\w -> 
                        ( Sel { unSel = \_ -> w},
                          Sel { unSel = \_ -> WriterT $ do
                                                (_, r) <- (runWriterT (w >>= gamma))
                                                return (r, mempty)} 
                        )) 
                        (fmap 
                            (\fa -> foldAlg 
                                    (sel2writer_ret (h_ret h) gamma) 
                                    (sel2writer_ops (h_ops h) gamma) 
                                    (fa >>= \a -> sel2free (q a) (h_ret h) gamma)
                            ) op
                        )
                )) gamma)   
            )}

    -- ???

    -- goal?
    === (h_ops h) (fmap ( \w -> ( handlerPRet h w 
                                , undefined) 
                        )                                         
                        (fmap (>>= q) (fmap (\fr -> Sel { unSel = \_ -> lift fr }) op))) 

    -- goal?
    === (h_ops h) (fmap ( \w -> ( handlerPRet h w 
                                , undefined) 
                        )                                         
                        (fmap (>>= q) (fmap (\fr -> Sel { unSel = \_ -> lift fr }) op)))   

    -- goal?
    -- === (h_ops h) (fmap ( \w -> ( handlerPRet h w 
    --                             , do
    --                                 (x, r1) <- silence (handlerPRet h w)
    --                                 r2 <- cont x
    --                                 return (r1 <> r2)) 
    --                     )                                         
    --                     (fmap (>>= q) (fmap (\fr -> Sel { unSel = \_ -> lift fr }) op)))

    -- HOS
    -- === (h_ops h) (fmap ( \p -> ( handlerG h cont p 
    --                             , do
    --                                 (x, r1) <- silence (handlerG h cont p)
    --                                 r2 <- cont x
    --                                 return (r1 <> r2)) 
    --                     )                                         
    --                     (fmap (>>= q) op))











-- 主定理の Handler case の補題 (Loss r p)
proofLemmaLoss :: (Monoid r, Show r, Ord r, Functor e, Functor es) 
    => Handler r e es a ans -> r -> (Sel r (e :* es) a) -> Sel r es ans
proofLemmaLoss h r q = 

        handlerPRet h ( loss r >> q )

    -- def of loss r
    === handlerPRet h ( Sel { unSel = (\_ -> tell r) } >> q )

    -- def of handlerPRet
    === Sel { unSel = (\gamma -> 
                foldAlg 
                    (sel2writer_ret (h_ret h) gamma) 
                    (sel2writer_ops (h_ops h) gamma)
                    (sel2free ( Sel { unSel = (\_ -> tell r) } >> q ) (h_ret h) gamma)
            )}
    
    -- def of sel2free
    === Sel { unSel = (\gamma -> 
                foldAlg 
                    (sel2writer_ret (h_ret h) gamma) 
                    (sel2writer_ops (h_ops h) gamma)
                    (runWriterT (unSel ( Sel { unSel = (\_ -> tell r) } >> q ) (\x -> 
                        writerTMap cast ((unSel ((h_ret h) x) gamma) >>= gamma)
                    )))
            )}

    -- def of >>= of SelN
    === Sel { unSel = (\gamma -> 
                foldAlg 
                    (sel2writer_ret (h_ret h) gamma) 
                    (sel2writer_ops (h_ops h) gamma)
                    (runWriterT (unSel ( Sel { unSel = (\p -> (\_ -> tell r) (\a -> unSel q p  >>= \y -> p y)
                                                                    >>= \x -> unSel q p) } ) (\x -> 
                        writerTMap cast ((unSel ((h_ret h) x) gamma) >>= gamma)
                    )))
            )}

    -- fun app
    === Sel { unSel = (\gamma -> 
                foldAlg 
                    (sel2writer_ret (h_ret h) gamma) 
                    (sel2writer_ops (h_ops h) gamma)
                    (runWriterT (unSel ( Sel { unSel = (\p -> tell r >>= \x -> unSel q p) } ) (\x -> 
                        writerTMap cast ((unSel ((h_ret h) x) gamma) >>= gamma)
                    )))
            )}

    -- def of >>= of WriterT
    === Sel { unSel = (\gamma -> 
                foldAlg 
                    (sel2writer_ret (h_ret h) gamma) 
                    (sel2writer_ops (h_ops h) gamma)
                    (runWriterT (unSel ( Sel { unSel = (\p -> WriterT $ do
                        (a, r1) <- runWriterT $ tell r
                        (b, r2) <- runWriterT $ unSel q p
                        pureE (b, r1 <> r2)) } ) (\x -> 
                        writerTMap cast ((unSel ((h_ret h) x) gamma) >>= gamma)
                    )))
            )}

    -- def of tell r
    === Sel { unSel = (\gamma -> 
                foldAlg 
                    (sel2writer_ret (h_ret h) gamma) 
                    (sel2writer_ops (h_ops h) gamma)
                    (runWriterT (unSel ( Sel { unSel = (\p -> WriterT $ do
                        (a, r1) <- runWriterT $ WriterT $ pureE ((), r)
                        (b, r2) <- runWriterT $ unSel q p
                        pureE (b, r1 <> r2)) } ) (\x -> 
                        writerTMap cast ((unSel ((h_ret h) x) gamma) >>= gamma)
                    )))
            )}

    -- runWriterT . WriterT / r1 = r
    === Sel { unSel = (\gamma -> 
                foldAlg 
                    (sel2writer_ret (h_ret h) gamma) 
                    (sel2writer_ops (h_ops h) gamma)
                    (runWriterT (unSel ( Sel { unSel = (\p -> WriterT $ do
                        (b, r2) <- runWriterT $ unSel q p
                        pureE (b, r <> r2)) } ) (\x -> 
                        writerTMap cast ((unSel ((h_ret h) x) gamma) >>= gamma)
                    )))
            )}

    -- unSel . Sel / fun app
    === Sel { unSel = (\gamma -> 
                foldAlg 
                    (sel2writer_ret (h_ret h) gamma) 
                    (sel2writer_ops (h_ops h) gamma)
                    (runWriterT ((WriterT $ do
                        (b, r2) <- runWriterT $ unSel q (\x -> writerTMap cast ((unSel ((h_ret h) x) gamma) >>= gamma))
                        pureE (b, r <> r2))))
            )}

    -- runWriterT . WriterT 
    === Sel { unSel = (\gamma -> 
                foldAlg 
                    (sel2writer_ret (h_ret h) gamma) 
                    (sel2writer_ops (h_ops h) gamma)
                    (do
                        (b, r2) <- runWriterT $ unSel q (\x -> writerTMap cast ((unSel ((h_ret h) x) gamma) >>= gamma))
                        pureE (b, r <> r2)
                    )  
            )}

    -- def of sel2free
    === Sel { unSel = (\gamma -> 
                foldAlg 
                    (sel2writer_ret (h_ret h) gamma) 
                    (sel2writer_ops (h_ops h) gamma)
                    (do
                        (b, r2) <- sel2free q (h_ret h) gamma
                        pureE (b, r <> r2)
                    )  
            )}

    -- do -> >>=
    === Sel { unSel = (\gamma -> 
                foldAlg 
                    (sel2writer_ret (h_ret h) gamma) 
                    (sel2writer_ops (h_ops h) gamma)
                    (sel2free q (h_ret h) gamma >>= \(b,r2) -> pureE (b, r <> r2))  
            )}

    -- fun abst
    === Sel { unSel = (\gamma -> 
                foldAlg 
                    (sel2writer_ret (h_ret h) gamma) 
                    (sel2writer_ops (h_ops h) gamma)
                    (sel2free q (h_ret h) gamma >>= \(b,r2) -> pureE . (\(a,b) -> (a, r <> b)) $ (b,r2))  
            )}

    -- p >>= pure . f = fmap f p
    === Sel { unSel = (\gamma -> 
                foldAlg 
                    (sel2writer_ret (h_ret h) gamma) 
                    (sel2writer_ops (h_ops h) gamma)
                    (do
                        fmap (\(a,b) -> (a, r <> b)) $
                            sel2free q (h_ret h) gamma
                            >>= \(b,r2) -> (pureE (b, r2))
                    )  
            )}

    -- p >>= return = p
    === Sel { unSel = (\gamma -> 
                foldAlg 
                    (sel2writer_ret (h_ret h) gamma) 
                    (sel2writer_ops (h_ops h) gamma)
                    (fmap (\(a,b) -> (a, r <> b)) $ sel2free q (h_ret h) gamma)  
            )}

    -- fmap-foldAlg lemma 
    === Sel { unSel = (\gamma -> 
                WriterT { runWriterT = (fmap (\(a, b) -> (a, r <> b)) $ 
                    runWriterT $ 
                        foldAlg
                            (sel2writer_ret (h_ret h) gamma) 
                            (sel2writer_ops (h_ops h) gamma)
                            (sel2free q (h_ret h) gamma)) }
                    )}

    -- p >>= pure . f = fmap f p
    === Sel { unSel = (\gamma -> 
                WriterT { runWriterT = 
                    runWriterT (foldAlg
                            (sel2writer_ret (h_ret h) gamma) 
                            (sel2writer_ops (h_ops h) gamma)
                            (sel2free q (h_ret h) gamma))
                        >>= \(b, r2) -> pureE . (\(a, b) -> (a, r <> b)) $ (b, r2) }
                    )}

    -- fun app
    === Sel { unSel = (\gamma -> WriterT $
                            runWriterT (foldAlg 
                                            (sel2writer_ret (h_ret h) gamma) 
                                            (sel2writer_ops (h_ops h) gamma)
                                            (sel2free q (h_ret h) gamma))
                                >>= \(b, r2) -> pureE (b, r <> r2) 
                        )}

    -- >>= -> do
    === Sel { unSel = (\gamma -> WriterT $ do 
                                    (x, r2) <- runWriterT $ foldAlg 
                                                    (sel2writer_ret (h_ret h) gamma) 
                                                    (sel2writer_ops (h_ops h) gamma)
                                                    (sel2free q (h_ret h) gamma)
                                    pureE (x, r <> r2)
                            )}

    -- runWriterT . WriterT / pure >>= law
    === Sel { unSel = (\gamma -> WriterT $ do
                                    (_, r1) <- runWriterT $ WriterT { runWriterT = (pure ((), r)) }
                                    (x, r2) <- runWriterT $ foldAlg 
                                                    (sel2writer_ret (h_ret h) gamma) 
                                                    (sel2writer_ops (h_ops h) gamma)
                                                    (sel2free q (h_ret h) gamma)
                                    pureE (x, r1 <> r2)
                            )}

    -- def (>>) of WriterT
    === Sel { unSel = (\gamma -> WriterT { runWriterT = (pure ((), r)) }
                            >> foldAlg 
                                    (sel2writer_ret (h_ret h) gamma) 
                                    (sel2writer_ops (h_ops h) gamma)
                                    (sel2free q (h_ret h) gamma)
                            )}

    -- def of tell r
    === Sel { unSel = (\gamma -> tell r
                        >> foldAlg 
                                (sel2writer_ret (h_ret h) gamma) 
                                (sel2writer_ops (h_ops h) gamma)
                                (sel2free q (h_ret h) gamma)
                           )}

    -- definition of (>>) of Sel
    === Sel { unSel = (\g -> tell r) } >> 
            Sel { unSel = 
                    (\gamma -> 
                        foldAlg 
                            (sel2writer_ret (h_ret h) gamma) 
                            (sel2writer_ops (h_ops h) gamma)
                            (sel2free q (h_ret h) gamma)
                    )}

    -- def of loss
    === loss r >> Sel { unSel = 
                (\gamma -> 
                    foldAlg 
                        (sel2writer_ret (h_ret h) gamma) 
                        (sel2writer_ops (h_ops h) gamma)
                        (sel2free q (h_ret h) gamma)
                )}
                
    -- def of handlerPRet 
    === loss r >> handlerPRet h q

    -- IH 
    -- === loss r >> handlerG h cont q






proofLemmaFoldAlgPure :: (Monoid r, Functor e, Functor es)
    => ((a, r) -> WriterT r (Eff es) ans)
    -> ((e :* es) (WriterT r (Eff es) ans) -> WriterT r (Eff es) ans)
    -> a -> r -> r
    -> Handler r e es a ans
    -> (ans -> WriterT r (Eff es) ())
    -> WriterT r (Eff es) ans
proofLemmaFoldAlgPure ret alg x r r' h gamma =
        foldAlg ret alg (fmap (\ (a , b) -> (a, r' <>  b)) (Pure (x,r)))
    === {- definition fmap -}
        foldAlg ret alg (Pure (x, r' <> r))
    === {- definition of foldAlg -}
        ret (x, r' <> r)
    === {- ret = (\(a, r) -> tell r >> unSel (ret a) gamma) -}
        tell (r' <> r) >> unSel (h_ret h x) gamma
    === {- tell (r' <> r) = tell r' >> tell r -}
        tell r' >> (tell r >> unSel (h_ret h x) gamma)
    === {- fold back -}
        tell r' >> foldAlg ret alg (Pure (x, r)) 
    === {- definition of >> and tell -}
        WriterT (do (x, r) <- runWriterT (foldAlg ret alg (Pure (x, r)))
                    pure (x, r' <> r))
    === {- defintion of fmap -}
    WriterT (fmap (\ (a, b) -> (a, r' <> b)) 
                  (runWriterT (foldAlg ret alg (Pure (x,r))) ) )




proofLemmaFoldAlgFreeR :: (Monoid r, Functor e, Functor es)
    => ((a, r) -> WriterT r (Eff es) ans)
    -> ((e :* es) (WriterT r (Eff es) ans) -> WriterT r (Eff es) ans)
    -> es (Free (e :* es) (a, r))
    -> r
    -> Handler r e es a ans
    -> (ans -> WriterT r (Eff es) ())
    -> WriterT r (Eff es) ans
proofLemmaFoldAlgFreeR ret alg op r' h gamma =
        foldAlg ret alg (fmap (\ (a , b) -> (a, r' <>  b)) (Free (RightEff op)))
    === {- definition of fmap -}
        (foldAlg ret alg (Free (fmap (fmap (\ (a , b) -> (a, r' <>  b))) (RightEff op))))
    === {- definition of foldAlg -}
        alg (fmap (foldAlg ret alg) (fmap (fmap (\ (a , b) -> (a, r' <>  b))) (RightEff op)))
    === {- fmap fusion -}
        alg (fmap (foldAlg ret alg . fmap (\ (a , b) -> (a, r' <>  b))) (RightEff op))
    === {- IH -}
        alg (fmap ( \p -> WriterT $ fmap (\(a, b) -> (a, r' <> b)) 
                                         (runWriterT (foldAlg ret alg p)) )
                  (RightEff op))
    === {- definition fmap -}
        alg ((RightEff $ fmap (\ p -> WriterT (fmap (\ (a, b) -> (a, r' <> b)) 
                                                    (runWriterT (foldAlg ret alg p)) )) 
                                op))
    === {- definition alg and (<+>) -}
        blg ( fmap (\ p -> WriterT $ (fmap (\ (a, b) -> (a, r' <> b)) 
                                        (runWriterT (foldAlg ret alg p)) )) 
                    op)
    === {- definition blg -}
        WriterT ( Free (fmap (\w -> runWriterT w) 
                                        (fmap (\ p -> WriterT (fmap (\ (a, b) -> (a, r' <> b)) 
                                                                    (runWriterT (foldAlg ret alg p)) )) 
                                                op) ) )
    === {- fmap fusion -}
        WriterT ( Free (fmap ((\w -> runWriterT w )
                                            . (\ p -> WriterT (fmap (\ (a, b) -> (a, r' <> b)) 
                                                                    (runWriterT (foldAlg ret alg p)) )) )
                                        op ) )
    === {- runWriterT . WriterT = id -}
    WriterT (Free (fmap (\ p -> fmap (\ (a, b) -> (a, r' <> b)) 
                                        (runWriterT (foldAlg ret alg p))) 
                             op)) 
    === {- definition fmap -}
    WriterT (fmap (\ (a, b) -> (a, r' <> b)) 
                (Free (fmap (\p -> (runWriterT ((foldAlg ret alg p)))) op) ))
    === {- fmap fission -}
    WriterT (fmap (\ (a, b) -> (a, r' <> b)) 
                (Free (fmap runWriterT 
                        (fmap (\p -> foldAlg ret alg p) op))))
    === {- runWriterT . WriterT = id -}
    WriterT (fmap (\ (a, b) -> (a, r' <> b)) 
                (runWriterT (WriterT (Free (fmap runWriterT 
                        (fmap (\p -> foldAlg ret alg p) op))))))
    === {- definition blg -}
        WriterT (fmap (\ (a, b) -> (a, r' <> b)) 
                    (runWriterT (blg (fmap (\p -> foldAlg ret alg p) op))))
    === {- definition of alg -}
        WriterT (fmap (\ (a, b) -> (a, r' <> b)) 
                    (runWriterT (alg (RightEff (fmap (\p -> foldAlg ret alg p) op)))))
    === {- definition fmap -}
        WriterT (fmap (\ (a, b) -> (a, r' <> b)) 
                    (runWriterT (alg (fmap (\p -> foldAlg ret alg p) (RightEff op)))))
    === {- definition e -}
        WriterT (fmap (\ (a, b) -> (a, r' <> b)) 
                    (runWriterT (alg (fmap (foldAlg ret alg) (RightEff op)))))           
    === {- definition foldAlg -}
        WriterT (fmap (\ (a, b) -> (a, r' <> b)) 
                    (runWriterT (foldAlg ret alg (Free (RightEff op)))))           






proofLemmaFoldAlgFreeL :: (Monoid r, Functor e, Functor es)
    => ((a, r) -> WriterT r (Eff es) ans)
    -> ((e :* es) (WriterT r (Eff es) ans) -> WriterT r (Eff es) ans)
    -> e (Free (e :* es) (a, r))
    -> r
    -> Handler r e es a ans
    -> (ans -> WriterT r (Eff es) ())
    -> WriterT r (Eff es) ans
proofLemmaFoldAlgFreeL ret alg op r' h gamma =
        foldAlg ret alg (fmap (\ (a , b) -> (a, r' <>  b)) (Free (LeftEff op)))
    === {- definition of fmap -}
        (foldAlg ret alg (Free (fmap (fmap (\ (a , b) -> (a, r' <>  b))) (LeftEff op))))
    === {- definition of foldAlg -}
        alg (fmap (foldAlg ret alg) (fmap (fmap (\ (a , b) -> (a, r' <>  b))) (LeftEff op)))
    === {- fmap fusion -}
        alg (fmap (foldAlg ret alg . fmap (\ (a , b) -> (a, r' <>  b))) (LeftEff op))
    === {- IH -}
        alg (fmap ( \p -> WriterT $ fmap (\(a, b) -> (a, r' <> b)) 
                                         (runWriterT (foldAlg ret alg p)) )
                  (LeftEff op))
    === {- definition fmap -}
        alg (LeftEff $ fmap (\ p -> WriterT $ (fmap (\ (a, b) -> (a, r' <> b)) 
                                                    (runWriterT (foldAlg ret alg p)) )) 
                            op)
    === {- definition alg and (<+>) -}
        unSel ((h_ops h) (fmap (\w -> 
                ( Sel $ \_ -> w
                , Sel $ \_ -> lift (fmap snd (runWriterT (w >>= gamma))) ) 
                               ) 
                               (fmap (\ p -> WriterT $ (fmap (\ (a, b) -> (a, r' <> b)) 
                                                             (runWriterT (foldAlg ret alg p)) )) 
                                     op)
              )) gamma

    -- ???

    === let f = (\ (a, b) -> (a, r' <> b)) 
            g = (\w -> 
                        ( Sel $ \_ -> w
                        , Sel $ \_ -> lift (fmap snd (runWriterT (w >>= gamma))) ) 
                                    )
        in 
        unSel ((h_ops h) (fmap g (fmap (\ p -> WriterT $ (fmap f (runWriterT (foldAlg ret alg p)) )) 
                                       op)
              )) gamma

    === let f = (\ (a, b) -> (a, r' <> b)) 
            g = (\w -> 
                        ( Sel $ \_ -> w
                        , Sel $ \_ -> lift (fmap snd (runWriterT (w >>= gamma))) ) 
                                    )
        in 
        unSel ((h_ops h) (fmap ( (\ p -> g (WriterT $ (fmap f (runWriterT (foldAlg ret alg p)) ))) 
                                    )op
              )) gamma


    === let f = (\ (a, b) -> (a, r' <> b)) 
        in 
        unSel ((h_ops h) (fmap ( (\ p -> 
                        ( Sel $ \_ -> (WriterT $ (fmap f (runWriterT (foldAlg ret alg p)) ))
                        , Sel $ \_ -> lift (fmap snd (runWriterT ((WriterT $ (fmap f (runWriterT (foldAlg ret alg p)) )) >>= gamma))) )) 
                                    ) op
              )) gamma

    === let f = (\ (a, b) -> (a, r' <> b)) 
        in 
        unSel ((h_ops h) (fmap ( (\ p -> 
                        ( Sel $ \_ -> (WriterT $ (fmap f (runWriterT (foldAlg ret alg p)) ))
                        , Sel $ \_ -> lift (fmap snd (runWriterT (
                                                        (WriterT $ (fmap f (runWriterT (foldAlg ret alg p)) )) >>= gamma
                                                                 )
                                                     )) )) 
                                    ) op
              )) gamma

    --- ???

    === let f = (\ (a, b) -> (a, r' <> b)) 
            g = (\w -> 
                        ( Sel $ \_ -> w
                        , Sel $ \_ -> lift (fmap snd (runWriterT (w >>= gamma))) ) 
                                    )
                       
        in 
        ( WriterT $
            fmap (\ (a, b) -> (a, r' <> b)) 
                 (runWriterT
                    (unSel ((h_ops h) (fmap g (fmap (foldAlg ret alg) op))) 
                            gamma)))


    -- ???


    === {- definition alg -}
        ( WriterT $
            fmap (\ (a, b) -> (a, r' <> b)) 
                 (runWriterT 
                    (unSel ((h_ops h) (fmap (\w -> 
                        ( Sel $ \_ -> w
                        , Sel $ \_ -> lift (fmap snd (runWriterT (w >>= gamma))) )
                                            ) (fmap (foldAlg ret alg) op) 
                            )) 
                            gamma)) )
    === {- definition alg -}
        WriterT (fmap (\ (a, b) -> (a, r' <> b)) 
                      (runWriterT (alg (LeftEff (fmap (foldAlg ret alg) op)))))
    === {- definition fmap -}
        WriterT (fmap (\ (a, b) -> (a, r' <> b)) 
                      (runWriterT (alg (fmap (foldAlg ret alg) (LeftEff op)))))
    === {- def of foldAlg -}
        WriterT (fmap (\ (a, b) -> (a, r' <> b)) 
                      (runWriterT (foldAlg ret alg (Free (LeftEff op))))) 























-- experiment

exAlg :: (Functor e, Monoid r, Num r, Ord r) => Max String (Sel r e b, Sel r e r) -> Sel r e b
exAlg (Max [s1, s2, s3] k) = do
    b <- (snd . k) s1
    if (b > 0) 
        then (fst . k) s1
        else (fst . k) s2

expr :: (Monoid r, Num r, Ord r) => Sel r (Max String :* VoidEff) String
expr = do
    loss 1
    s <- maxE ["aaa", "aabb"]
    return s 


expr' :: (Monoid r, Num r, Ord r) => Sel r (Max String :* VoidEff) String
expr' = do
    Sel { unSel = (\_ -> tell 1) } >>= \_ -> Sel { unSel = \_ -> lift ((Free . inj) (Max ["aaa", "aabb"] Pure)) } 


expr'' :: (Monoid r, Num r, Ord r) => Sel r (Max String :* VoidEff) String
expr'' = do
    Sel { unSel = 
            ( \p -> WriterT $ do 
                    (b, r2) <- runWriterT $ lift ((Free . inj) (Max ["aaa", "aabb"] Pure))
                    return (b, 1 <> r2)
            )   } 
    -- p appeares nowhere 
    -- loss happend before affect resulting loss value


experiment :: (Monoid r, Num r, Ord r) => Sel r VoidEff String
experiment = 
        SelN.hEx SelN.experiment

    === handlerP exAlg expr

    === let exH = H { h_ret = (return), h_ops = exAlg }  
        in handlerPRet exH expr
            
    === let exH = H { h_ret = (return), h_ops = exAlg }  
        in Sel { unSel = 
                (\gamma -> 
                    foldAlg 
                        (sel2writer_ret (h_ret exH) gamma) 
                        (sel2writer_ops (h_ops exH) gamma)
                        (sel2free expr (h_ret exH) gamma)
                )}
    
    === let exH = H { h_ret = (return), h_ops = exAlg } 
            expr = Sel { unSel = 
                        ( \_ -> WriterT $ do 
                                (b, r2) <- runWriterT $ lift ((Free . LeftEff) (Max ["aaa", "aabb"] Pure))
                                return (b, 1 <> r2)
                        )   } 
        in Sel { unSel = 
                (\gamma -> 
                    foldAlg 
                        (sel2writer_ret (h_ret exH) gamma) 
                        (sel2writer_ops (h_ops exH) gamma)
                        (runWriterT (unSel expr (\x -> 
                            writerTMap cast ((unSel ((h_ret exH) x) gamma) >>= gamma) -- ???
                        )))
                )}

    === let exH = H { h_ret = (return), h_ops = exAlg }   
        in Sel { unSel = 
                (\gamma -> 
                    foldAlg 
                        (sel2writer_ret (h_ret exH) gamma) 
                        (sel2writer_ops (h_ops exH) gamma)
                        (do (b, r2) <- runWriterT $ WriterT $ do
                                                    a <- ((Free . LeftEff) (Max ["aaa", "aabb"] Pure))
                                                    return (a, mempty)
                            return (b, 1 <> r2))
                )}

    === let exH = H { h_ret = (return), h_ops = exAlg }   
        in Sel { unSel = 
                (\gamma -> 
                    foldAlg 
                        (sel2writer_ret (h_ret exH) gamma) 
                        (sel2writer_ops (h_ops exH) gamma)
                        (do b <- ((Free . LeftEff) (Max ["aaa", "aabb"] Pure))
                            return (b, 1))
                )}

    === let exH = H { h_ret = (return), h_ops = exAlg }   
        in Sel { unSel = 
                (\gamma -> 
                    foldAlg 
                        (sel2writer_ret (h_ret exH) gamma) 
                        (sel2writer_ops (h_ops exH) gamma)
                        (do Free (fmap (>>= (\b -> return (b, 1))) (LeftEff (Max ["aaa", "aabb"] Pure))) )
                )}

    === let exH = H { h_ret = (return), h_ops = exAlg }
            e   = (fmap (>>= (\b -> return (b, 1))) (LeftEff (Max ["aaa", "aabb"] Pure)))
        in Sel { unSel = 
                (\gamma -> 
                    (sel2writer_ops (h_ops exH) gamma) (fmap (foldAlg (sel2writer_ret (h_ret exH) gamma) (sel2writer_ops (h_ops exH) gamma)) e)
                )}

    === let exH = H { h_ret = (return), h_ops = exAlg }
            e   = (LeftEff (Max ["aaa", "aabb"] (\b -> return (b, 1))))
        in Sel { unSel = 
                (\gamma -> 
                    ((\hw -> unSel ((h_ops exH) (fmap (\w -> 
                            ( Sel { unSel = \_ -> w},
                              Sel { unSel = \_ -> lift (fmap snd (runWriterT (w >>= gamma)))} )
                                            ) hw)) gamma) 
                                    <+> blg) 
                    (fmap (foldAlg (sel2writer_ret (h_ret exH) gamma) (sel2writer_ops (h_ops exH) gamma)) e)
                )}

    === let exH = H { h_ret = (return), h_ops = exAlg }
        in Sel { unSel = 
                (\gamma -> 
                    ((\hw -> unSel ((h_ops exH) (fmap (\w -> 
                            ( Sel { unSel = \_ -> w},
                              Sel { unSel = \_ -> lift (fmap snd (runWriterT (w >>= gamma)))} )
                                            ) hw)) gamma) 
                                    <+> blg) 
                    ( LeftEff (fmap (foldAlg (sel2writer_ret (h_ret exH) gamma) (sel2writer_ops (h_ops exH) gamma)) 
                                    (Max ["aaa", "aabb"] (\b -> return (b, 1)))) )
                )}

    === let exH = H { h_ret = (return), h_ops = exAlg }
        in Sel { unSel = 
                (\gamma -> 
                    ((\hw -> unSel ((h_ops exH) (fmap (\w -> 
                            ( Sel { unSel = \_ -> w},
                              Sel { unSel = \_ -> lift (fmap snd (runWriterT (w >>= gamma)))} )
                                            ) hw)) gamma) 
                                    <+> blg) 
                    ( LeftEff ( Max ["aaa", "aabb"] ((\p -> foldAlg (sel2writer_ret (h_ret exH) gamma) (sel2writer_ops (h_ops exH) gamma) (Pure (p, 1)) )))) 
                )}

    === let exH = H { h_ret = (return), h_ops = exAlg }
        in Sel { unSel = 
                (\gamma -> 
                    ((\hw -> unSel ((h_ops exH) (fmap (\w -> 
                            ( Sel { unSel = \_ -> w},
                              Sel { unSel = \_ -> lift (fmap snd (runWriterT (w >>= gamma)))} )
                                            ) hw)) gamma) 
                                    <+> blg) 
                    ( LeftEff ( Max ["aaa", "aabb"] ((\p -> (sel2writer_ret (h_ret exH) gamma) (p, 1) )))) 
                )}

    === let exH = H { h_ret = (return), h_ops = exAlg }
        in Sel { unSel = 
                (\gamma -> 
                    ((\hw -> unSel ((h_ops exH) (fmap (\w -> 
                            ( Sel { unSel = \_ -> w},
                              Sel { unSel = \_ -> lift (fmap snd (runWriterT (w >>= gamma)))} )
                                            ) hw)) gamma) 
                                    <+> blg) 
                    ( LeftEff ( Max ["aaa", "aabb"] (\p -> (tell 1 >> unSel (return p) gamma) ))) 
                )}
    
    === let exH = H { h_ret = (return), h_ops = exAlg }
        in Sel { unSel = 
                (\gamma -> 
                    ((\hw -> unSel ((h_ops exH) (fmap (\w -> 
                            ( Sel { unSel = \_ -> w},
                              Sel { unSel = \_ -> lift (fmap snd (runWriterT (w >>= gamma)))} )
                                            ) hw)) gamma) 
                                    <+> blg) 
                    ( LeftEff ( Max ["aaa", "aabb"] (\p -> ( WriterT $ Pure (p, 1) ))) )
                )}

    === let exH = H { h_ret = (return), h_ops = exAlg }
        in Sel { unSel = 
                (\gamma -> 
                    (unSel ((h_ops exH) (fmap (\w -> 
                            ( Sel { unSel = \_ -> w},
                              Sel { unSel = \_ -> lift (fmap snd (runWriterT (w >>= gamma)))} )
                                            ) (Max ["aaa", "aabb"] (\p -> ( WriterT $ Pure (p, 1) ))))) gamma) 
                )}

    === let exH = H { h_ret = (return), h_ops = exAlg }
        in Sel { unSel = 
                (\gamma -> 
                    (unSel ((h_ops exH) ((Max ["aaa", "aabb"] ( (\w -> 
                            ( Sel { unSel = \_ -> w},
                              Sel { unSel = \_ -> lift (fmap snd (runWriterT (w >>= gamma)))} )
                                            ) . (\p -> WriterT $ Pure (p, 1) ))))) gamma) 
                )}

    === let exH = H { h_ret = (return), h_ops = exAlg }
        in Sel { unSel = 
                (\gamma -> 
                    (unSel ((h_ops exH) (Max ["aaa", "aabb"] ( \w -> 
                            ( Sel { unSel = \_ -> WriterT $ Pure (w, 1)},
                              Sel { unSel = \_ -> lift (fmap snd (runWriterT ((WriterT $ Pure (w, 1)) >>= gamma)))} )
                                            ) 
                                        )
                            ) gamma) 
                )}

    === Sel { unSel = 
                (\gamma -> 
                    (unSel (do
                            b <- (\w -> Sel { unSel = \_ -> lift (fmap snd (runWriterT ((WriterT $ Pure (w, 1)) >>= gamma)))}) "aaa"
                            if (b > 0) 
                                then (\w -> Sel { unSel = \_ -> WriterT $ Pure (w, 1)}) "aaa"
                                else (\w -> Sel { unSel = \_ -> WriterT $ Pure (w, 1)}) "aabb" 
                            ) gamma) 
                )}

    === Sel { unSel = 
                (\gamma -> 
                    (unSel (do
                            b <- ( Sel { unSel = \_ -> lift (fmap snd (( do
                                        (b,r2) <- runWriterT $ gamma "aaa"
                                        return (b, 1 <> r2)
                                )))}) 
                            if (b > 0) 
                                then (\w -> Sel { unSel = \_ -> WriterT $ Pure (w, 1)}) "aaa"
                                else (\w -> Sel { unSel = \_ -> WriterT $ Pure (w, 1)}) "aabb" 
                            ) gamma) 
                )}



experiment' :: (Monoid r, Num r, Ord r) => (String, r)
experiment' = 
        SelN.runSel $ SelN.hEx SelN.experiment
    
    === (SelN.runSel $ Sel { unSel = 
                (\gamma -> 
                    (unSel (do
                            b <- ( Sel { unSel = \_ -> lift (fmap snd (( do
                                        (b,r2) <- runWriterT $ gamma "aaa"
                                        return (b, 1 <> r2)
                                )))}) 
                            if (b > 0) 
                                then (\w -> Sel { unSel = \_ -> WriterT $ Pure (w, 1)}) "aaa"
                                else (\w -> Sel { unSel = \_ -> WriterT $ Pure (w, 1)}) "aabb" 
                            ) gamma) 
                )})