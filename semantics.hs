{-# LANGUAGE DeriveGeneric #-}
{-|
Module      : RuleTreeSemantics
Description : Contains the syntax, semantics and trace semantics for ruletree
Copyright   : (c) Nico Naus, 2017
Maintainer  : n.naus@uu.nl
Stability   : experimental

This module defines a tree structure for describing rule based problems,
together with a semantics for application of these trees, and a trace semantics
to calculate the steps possible.

There are also solving algorithms, practical examples, and quickcheck properties included
-}
module RuleTreeSemantics where

import Data.Maybe
import Test.QuickCheck
import Test.QuickCheck.Arbitrary.ADT
import GHC.Generics
import qualified Data.Set as S
import qualified Data.Map as M



-- Functions that you can run to test this module

--example problems:
-- | Runs the minMax solver to solve the TicTacToe example
solveTTT = minMaxTrace True goalp1 goalp2 goalTie 6 playTTT exampleGame  -- WORKS
-- | Runs the heuristic solver to solve the c&c example
solveShipHeur = heuristicTrace shipNotOnFire shipScore [(shipTree ,testState,[])] -- Works!

--QuickCheck properties:

check     = quickCheckWith   stdArgs {maxSize = 3, maxSuccess = 100000} rtEquality

-- check rtEquality with a generator that builds more sensible ruleTrees (where a = list of int)
genCheck = quickCheckWith   stdArgs {maxSize = 3, maxSuccess = 100000} (forAll genPar (\x -> rtEquality x [0,0,0,0,0]))

--types and instances

data RuleTree a 
  -- | Put 'RuleTree's in sequence
  = Seq      [RuleTree a]
  -- | Choose among 'RuleTree's
  | Choice   [RuleTree a]
  -- | Allow parallel execution of 'RuleTree's
  | Parallel [RuleTree a]
  -- | Assign a 'RuleTree' to a 'User'
  | Assign   User         (RuleTree a)
  | Leaf     (Rule a)
  | Empty                  deriving (Show, Generic)

instance (CoArbitrary a, Arbitrary a) => Arbitrary (RuleTree a) where
      arbitrary = genericArbitrary


data Rule a = Rule           Name (Effect a)
            | AssRule   User Name (Effect a) 
            | Condition      Name (a->Bool)  (Rule a) deriving Generic

instance (Arbitrary a , CoArbitrary a) => Arbitrary (Rule a) where
      arbitrary = oneof [ do
                           x <- arbitrary
                           return (Rule "r" x)
                        , do
                           x <- arbitrary
                           u <- arbitrary
                           return (AssRule u "r" x)
                        , do
                           p <- arbitrary
                           r <- arbitrary
                           return (Condition "" p r)]

instance Show (Rule a) where 
      show (Rule        n e) = n
      show (AssRule   u n e) = show u ++ "@" ++ n
      show (Condition n p r) = "Condition " ++ n ++ show r


type RuleSet a = [Rule a]            
type Name = String
type Effect a = a -> a
type Goal a = a -> Bool
data User = User String deriving (Show, Eq, Ord)
instance Arbitrary User where
      arbitrary = elements [User "u1", User "u2", User "u3", User "u4"]

data Trace a = Step a (RuleSet a) (Trace a)
             | End a deriving Show

-- Auxiliariy functions

-- | Converts rules to their effect function
ruleToEffect ::  (Rule a)           ->  (a -> a)
ruleToEffect     (Rule _ e)         =   e
ruleToEffect     (AssRule _ _ e)    =   e
ruleToEffect     (Condition _ _ r)  =   ruleToEffect r

-- | Application of RuleSet to state
appRSet :: RuleSet a ->           a             -> Maybe a
appRSet    []                     s             =  Just s
appRSet    ((Rule n e)     :xs)   s             =  appRSet xs (e s)
appRSet    ((AssRule u n e):xs)   s             =  appRSet xs (e s)
appRSet    ((Condition n p r):xs) s | p s       =  appRSet (r:xs) s
                                    | otherwise =  Nothing

-- | union of two maybes, in accordance of definition of Fail
union :: Maybe [a] -> Maybe [a] -> Maybe [a]
union    Nothing      Nothing   =  Nothing
union    Nothing      (Just x)  =  Just x
union    (Just x)     Nothing   =  Just x
union    (Just x)     (Just y)  =  Just $ x++y

-- | Special version of catMaybes that uses union to perform the folding
catMaybes' :: [Maybe [a]] -> Maybe [a]
catMaybes' = foldr union Nothing

-- | Converts a maybe list to a list, empty when Nothing
maybeListToList :: Maybe [a]  ->  [a]
maybeListToList    Nothing    =   []
maybeListToList    (Just x)   =   x

-- | Returns the first ruleset of a trace
traceToHint :: Trace a -> RuleSet a
traceToHint (Step _ rset _) = rset
traceToHint (End       _)   = []

-- | Converts a list of states and rulesets to a trace
listToTrace :: Eq a => [(a,RuleSet a)] -> a -> Trace a
listToTrace [] s = End s
listToTrace ((s,rset):xs) s' = Step s rset (listToTrace xs s')

-- | Converts traces to lists of leaves
tracesToLeaf :: [Trace a] -> [a]
tracesToLeaf [] = []
tracesToLeaf ((End s):xs) = [s] ++ tracesToLeaf xs
tracesToLeaf ((Step _ _ t):xs) = tracesToLeaf (t:xs)

-- | Converts traces to list of rulesets
tracesToSteps :: [Trace a] -> [[RuleSet a]]
tracesToSteps [] = []
tracesToSteps tr = map traceToSteps tr

-- | Converts a trace to a list of rulesets
traceToSteps :: Trace a -> [RuleSet a]
traceToSteps (End s) = []
traceToSteps (Step _ rset x) = [rset] ++ traceToSteps x

--Semantics RuleTree application

-- | takes a RuleTree and a state, and produces a list of all possible endstates
appRT :: RuleTree a ->         a -> Maybe [a]
appRT (Seq (rt:rts))           s = case appRT rt s of
                                     Just x -> catMaybes' $ map (appRT (Seq rts)) x
                                     Nothing -> Nothing
appRT (Seq [])                 s = Just [s]
appRT (Choice (rt:rts))        s = catMaybes' ((appRT rt s):[(appRT (Choice rts)s)])
appRT (Choice [])              _ = Nothing
appRT (Parallel (rt:rts))      s = case oneStep (Parallel (rt:rts)) of
                                    [] -> Nothing
                                    x  -> catMaybes' $ concat [case appRT r s of {Nothing -> [Nothing];Just x -> map (appRT rt') x}|(r,rt')<- x]
appRT (Parallel [])            s = Just [s]  
appRT (Assign u rt)            s = appRT rt s                             
appRT (Leaf (Rule n e))        s = Just [e s]
appRT (Leaf (AssRule  u n e))  s = Just [e s]
appRT (Leaf (Condition _ p r)) s | p s = appRT (Leaf r) s
                                 | otherwise = Nothing
appRT Empty                    s = Just [s]



-- | Takes a rulestree and produces a list of pairs of first steps and ruletrees
oneStep :: RuleTree a      -> [(RuleTree a, RuleTree a)]
oneStep (Seq (rt:rts))      = concat [case (r,rt') of {(Empty,Empty) -> oneStep (Seq rts);
                                                       --(Empty,_)->oneStep (Seq (rt':rts));
                                                       x->[(r,Seq(rt':rts))]}
                                     |(r,rt')<-oneStep rt]
oneStep (Seq [])            = [(Empty,Empty)]
oneStep (Choice (rt:rts))   = oneStep rt ++ oneStep (Choice rts)
oneStep (Choice [])         = []
oneStep (Parallel (rt:rts)) = concat [case (r,rt') of {(Empty,Empty) -> oneStep (Parallel rts);
                                                       --(Empty,_)     -> oneStep (Parallel (rt':rts));
                                                       x             -> [(r,Parallel (rt':rts))] ++ [(r',Parallel(rt:rts'))|(r',Parallel rts')<-oneStep (Parallel rts)]} --when onstep rts is empty, the last case is never produced!!
                                     |(r,rt')<-oneStep rt] 
oneStep (Parallel [])       = [(Empty        ,Empty)]
oneStep (Assign u rt)       = oneStep rt
oneStep (Leaf r)            = [(Leaf r       ,Empty)]
oneStep Empty               = [(Empty        ,Empty)]


--Semantics RuleTree steps

-- | Takes a ruletree and state and produces a list of all first rulesets that apply
firsts :: Eq a => RuleTree a -> a -> Maybe [(RuleSet a, RuleTree a)]
firsts (Seq (rt:rts))           s = case firsts rt s of 
                                      Nothing -> Nothing
                                      Just [] -> case firsts (Seq rts) s of
                                                  Nothing -> Nothing
                                                  Just y  -> Just [(rset, rts')| (rset,rts') <- y]
                                      Just x  -> case firsts (Seq rts) s of
                                                  Nothing -> Just [(rset,Seq (rt':rts))|(rset,rt')<-x]
                                                  Just y  -> Just $ [(rset,Seq (rt':rts))|(rset,rt')<-x] ++ [(rset, rt')|empty rt, (rset, rt')<- y]                                     
firsts (Seq [])                 _ = Just []
firsts (Choice (rt:rts))        s = firsts rt s `union` firsts (Choice rts) s
firsts (Choice [])              s = Nothing
firsts (Parallel [])            s = Just []
firsts (Parallel (rts))         s = (parPow rts s)
firsts (Assign u rt)            s = firsts (applyAssign rt u) s
firsts (Leaf r)                 _ = Just [([r],Empty)]
firsts Empty                    s = Just []                                                                           

-- | takes a ruletree and state, and determines if it is "ready"
empty :: RuleTree a ->        Bool
empty (Seq       [])          = True
empty (Seq       (rt:rts))    = empty rt && empty (Seq rts)
empty (Choice    [])          = False
empty (Choice    (rt:rts))    = empty rt || empty (Choice rts)
empty (Parallel  [])          = True
empty (Parallel  (rt:rts))    = empty rt && empty (Parallel rts)
empty (Assign    u        rt) = empty rt
empty (Leaf      r)           = False
empty Empty                   = True


-- | Takes a ruletree and state, and returns all possible parallel rulesets and the tree that belongs to it
parPow :: Eq a => [RuleTree a] -> a -> Maybe [(RuleSet a, RuleTree a)]
parPow            []              _ =  Just []
parPow            rts             s =  if parPowCrash firstsMap then Nothing else Just $ map (\(x,y) -> (x,Parallel y)) (parPowHelper ([],[]) (firstsMap) rts s)
                                         where firstsMap = map (\rt -> firsts rt s) rts
                                               parPowCrash x = case catMaybes' x of
                                                                 Nothing -> True
                                                                 Just [] -> elem' x
                                                                 _       -> False
                                               elem' [] = False
                                               elem' (Nothing:xs) = True
                                               elem' ((Just _):xs) = elem' xs

-- | takes the result so far, the list of firsts, the list of old ruletrees and returns 
parPowHelper :: Eq a => (RuleSet a, [RuleTree a]) -> [Maybe [(RuleSet a, RuleTree a)]] -> [RuleTree a] -> a -> [(RuleSet a, [RuleTree a])]
parPowHelper ([],x)      []             []       s = []
parPowHelper res         []             []       s = [res]
parPowHelper res         []             _        s = error "Optionlist and rts do not align, rts is longer"
parPowHelper res         _              []       s = error "Optionlist and rts do not align, Optionlist is longer"
parPowHelper (rset,rts') (Nothing:xs)   (rt:rts) s = parPowHelper (rset,rts'++[rt]) xs rts s
parPowHelper (rset,rts') ((Just []):xs) (rt:rts) s = parPowHelper (rset,rts'++[rt]) xs rts s
parPowHelper (rset,rts') ((Just x):xs)  (rt:rts) s = concat $ concat [[parPowHelper (rset++rset',rts'++[rt']) xs rts s|independentRuleSets rset rset' s]|(rset',rt')<-x]
                                                     ++ [parPowHelper (rset,rts'++[rt]) xs rts s]
                                                

-- | takes two rulesets and checks that 1) their effects are independent 2) they do not contain more than one rule per user
independentRuleSets :: Eq a => (RuleSet a) -> (RuleSet a) -> a -> Bool
independentRuleSets rset rset' s = and (concat ((map (\r1 -> map (\r2 -> independentRules r1 r2 s) rset') rset )))
                                 && not (or (map (usrInRuleSet rset) (ruleSetToUserID rset')))
                                 && not (containsUnAss rset && containsUnAss rset')
                                      where
                                        ruleSetToUserID [] = []
                                        ruleSetToUserID ((Rule _ _):xs) = ruleSetToUserID xs
                                        ruleSetToUserID ((AssRule u _ _):xs) = [u] ++ ruleSetToUserID xs
                                        ruleSetToUserID ((Condition n p r):xs) = ruleSetToUserID (r:xs)
                                        usrInRuleSet [] u = False
                                        usrInRuleSet ((Rule _ _) :xs) u  = usrInRuleSet xs u
                                        usrInRuleSet ((AssRule ur _ _):xs) u | u == ur = True
                                                                             | otherwise = usrInRuleSet xs u
                                        usrInRuleSet ((Condition _ _ r) :xs) u  = usrInRuleSet (r:xs) u
                                        containsUnAss [] = False
                                        containsUnAss ((Rule _ _) : xs) = True
                                        containsUnAss (x:xs) = containsUnAss xs
                                        independentRules r1 r2 s = (e1(e2 s)) == (e2 (e1 s))
                                                                    where
                                                                      e1 = ruleToEffect r1
                                                                      e2 = ruleToEffect r2

-- | Propagates assigning of a user one level
applyAssign :: RuleTree a -> User -> RuleTree a
applyAssign (Seq rts)              u = Seq [Assign u rt|rt<-rts]
applyAssign (Choice rts)           u = Choice [Assign u rt|rt<-rts]
applyAssign (Parallel rts)         u = Parallel [Assign u rt|rt<-rts]
applyAssign (Assign u rt)          _ = Assign u rt
applyAssign (Leaf r)               u = Leaf $ applyAssignLeaf r u
applyAssign Empty                  _ = Empty 

applyAssignLeaf :: Rule a -> User -> Rule a
applyAssignLeaf (Rule n e) u = AssRule u n e
applyAssignLeaf (AssRule u n e) _ = AssRule u n e
applyAssignLeaf (Condition n p r) u = Condition n p (applyAssignLeaf r u)

--Functioinality derived from firsts and empty

-- | expands a ruletree and state one level
expand :: Eq a => RuleTree a -> a -> Maybe [(RuleSet a,a,RuleTree a)]
expand rt s = case firsts rt s of
                 Nothing -> Nothing
                 Just x  -> catMaybes' [case appRSet rset s of {Nothing -> Nothing; Just y -> Just [(rset,y,rt')]}|(rset,rt')<-x]


-- | expands the ruletree and state untill the tree is completely consumed
traces :: Eq a => RuleTree a -> a -> [Trace a]
traces rt s = [End s | empty rt] 
              ++ case expand rt s of
                  Nothing -> []
                  Just [] -> []
                  Just x  -> concat [[Step s rset tr|tr <- (traces rt' s')]| (rset,s',rt')<-x]


-- Solving algorithms

-- | Performs breadth first search
breadthFirstTrace :: Eq a => Goal a -> [(RuleTree a, a, [(a,RuleSet a)])] -> [Trace a]
breadthFirstTrace g e = case [(x,s) | (rt,s,x) <- e, g s] of
                        [] ->  breadthFirstTrace g (concat [[ (rt',s',x ++ [(s,rset)])| (rset, s', rt')<- maybeListToList (expand rt s)]| (rt,s,x) <- e])
                        tr -> map (\(x,s) -> listToTrace x s) tr

-- | Performs best first (or A*) search
heuristicTrace :: Eq a => Goal a -> (a -> Int) -> [(RuleTree a, a, [(a,RuleSet a)])] -> [Trace a]
heuristicTrace g h e = case [(x,s) | (rt,s,x) <- e, g s] of
                         [] -> heuristicTrace g h ([(rt',s',x ++ [(s,rset)])|(rset, s', rt')<- maybeListToList (expand rt s)] ++ (high)) where ((rt,s,x),high) = splitOnScore e h Nothing
                         tr -> map (\(x,s) -> listToTrace x s) tr
                        where
                          splitOnScore []              _  Nothing                 = error "splitOnScore called without list so split and without candidates"
                          splitOnScore ((rt,s,tr):xs)  h  Nothing                 = splitOnScore xs h (Just (h s +traceCost tr, (rt,s,tr),[]))
                          splitOnScore []              _  (Just (i,low,high))     = (low,high)
                          splitOnScore ((rt,s,tr):xs)  h  (Just (i,low,high)) | h s + traceCost tr <  i = splitOnScore xs h (Just (h s + traceCost tr, (rt,s,tr),low:high))
                                                                              | otherwise               = splitOnScore xs h (Just (i, low, (rt,s,tr):high))
                          traceCost [] = 0
                          traceCost ((_,rset):xs) = length rset + traceCost xs

-- | Uses the MinMax algorithm to find the best trace
minMaxTrace :: Eq a => Bool -> Goal a -> Goal a -> Goal a -> Int -> RuleTree a -> a -> [(Int,Trace a)]
minMaxTrace turn g1 g2 g0 depth rt s 
  | ((depth == 0 ) && turn) = [((-1),End s)]
  | depth == 0              = [(3,End s)]
  | g1 s = [(2,End s)]
  | g2 s = [(0,End s)]
  | g0 s = [(1,End s)]
  | otherwise = case expand rt s of
                  Nothing -> []
                  Just [] -> []
                  Just x  -> concat [[(n,Step s rset tr) |(n,tr)<-helper turn (minMaxTrace (not turn) g1 g2 g0 (depth -1) rt' s')]| (rset,s',rt')<- x]
                               where
                                 helper _ [] = []
                                 helper True trlist = case filter (\(n,_)-> n==2) trlist of
                                                        [] -> case filter (\(n,_)-> n==1) trlist of
                                                                [] -> trlist
                                                                x  -> x
                                                        x  -> x
                                 helper False trlist = case filter (\(n,_)-> n==0) trlist of
                                                         [] -> case filter (\(n,_)-> n==1) trlist of
                                                                 [] -> trlist
                                                                 x  -> x
                                                         x  -> x

--Combinators

-- | takes an Int and a ruletree, and puts that ruletree in sequence that many times
times :: Int -> RuleTree a -> RuleTree a
times n rt = Seq (take n (repeat rt))



--Examples


-- TicTacToe

data TicTacToe = TicTacToe [[Maybe TicTac]] User User Bool deriving (Eq, Show) --board, player1, player2, turn (is player 1 playing?)
data TicTac = Tic | Tac deriving (Eq, Show)

alice = User "Alice"
bob   = User "Bob"

exampleGame :: TicTacToe
exampleGame = TicTacToe tttexample alice bob True

emptyBoard :: [[Maybe TicTac]]
emptyBoard = replicate 3 (replicate 3 Nothing)
tttexample = [[Just Tic,Just Tic, Nothing],[Just Tac,Nothing, Nothing],[Just Tic, Nothing, Nothing]]

playTTT :: RuleTree TicTacToe
playTTT = times 9 $ Seq [doTurn alice, doTurn bob]

doTurn :: User -> RuleTree TicTacToe
doTurn u = Assign u (Choice (map (\c -> Leaf (Condition "" (isFree c) (Rule ("Mark " ++ show c) (markTTT c))))
                                 (concat (map (\x -> (map (\y -> (x,y))[0..2]))[0..2]))))

isFree :: (Int,Int) -> TicTacToe -> Bool
isFree (x,y) (TicTacToe board _ _ _) = (board!!y)!!x == Nothing

markTTT :: (Int,Int) -> TicTacToe -> TicTacToe
markTTT (x,y) (TicTacToe board p1 p2 turn) = TicTacToe (updateAt y (updateAt x (Just Tic) (board!!y)) board) p1 p2 (not turn)

goalp1 (TicTacToe b p1 p2 t) = (elem [Just Tic,Just Tic,Just Tic] ((rows b) ++ (colums b) ++ (diags b))) && (not t)

goalp2 (TicTacToe b p1 p2 t)= (elem [Just Tac,Just Tac,Just Tac] ((rows b) ++ (colums b) ++ (diags b))) && t

goalTie (TicTacToe b p1 p2 t) = (filter (\cell -> cell == Nothing) (concat b))== []


rows b = b
colums b = [[b!!0!!0,b!!1!!0,b!!2!!0],[b!!0!!1,b!!1!!1,b!!2!!1],[b!!0!!2,b!!1!!2,b!!2!!2]] 
diags b = [[b!!0!!0,b!!1!!1,b!!2!!2],[b!!0!!2,b!!1!!1,b!!2!!0]] 

updateAt :: Int -> a -> [a] -> [a]
updateAt 0 val (x:xs) = val:xs
updateAt i val (x:xs) = (x:(updateAt (i-1) val xs))



--command and control (ship example)

data SimulationState = SimulationState ShipMap (M.Map User Agent) deriving (Eq, Show)
data Agent = Agent RoomNumber Inventory User deriving (Eq, Show)
data Inventory = NoItem | Extinguisher deriving (Eq, Show)
type ShipMap = [[Room]]
data Room = Room RoomNumber (Int,Int) [Exit] Inventory RoomState Int deriving (Eq, Show) --last int is width
data RoomState = Normal | Fire deriving (Eq, Show)         
type RoomNumber = Int
data Exit = ENorth RoomNumber
          | EEast  RoomNumber
          | ESouth RoomNumber
          | EWest  RoomNumber deriving (Eq, Show)

shipNotOnFire :: SimulationState -> Bool
shipNotOnFire (SimulationState s _) = not (foldr (||) False (map (onFire) (concat s)))

onFire :: Room -> Bool
onFire (Room _ _ _ _ s _) = s == Fire

findRoom :: [Room] -> RoomNumber -> Room
findRoom ((Room nr p e inv rs w):xs) i | nr == i = (Room nr p e inv rs w)
                                       | otherwise = findRoom xs i
                              
exitToNr (ENorth i) = i
exitToNr (EEast i) = i
exitToNr (ESouth i) = i
exitToNr (EWest i) = i

applyMove :: User -> RoomNumber -> SimulationState -> SimulationState
applyMove usr i (SimulationState s w) = SimulationState s (M.insert usr (Agent i holds usr) w)
                 where Agent position holds _ = w M.! usr

applyPickup :: User -> SimulationState -> SimulationState
applyPickup usr (SimulationState s w) = SimulationState (updateRoom s pos (Room pos coord exits NoItem roomState roomWidth)) (M.insert usr (Agent pos Extinguisher usr) w)
                where Room _ coord exits _ roomState roomWidth = findRoom (concat s) pos
                      Agent pos holds urs = w M.! usr

updateRoom :: ShipMap -> RoomNumber -> Room -> ShipMap
updateRoom [] _ _ = []
updateRoom (x:xs) n r  = [updateSubRoom x n r] ++ updateRoom xs n r
              where
                updateSubRoom :: [Room] -> RoomNumber -> Room -> [Room]
                updateSubRoom [] _ _ = []
                updateSubRoom ((Room number c e i s w):ys) n r | number == n = [r] ++ updateSubRoom ys n r
                                                               | otherwise = [(Room number c e i s w)] ++ updateSubRoom ys n r
canMove :: User -> RoomNumber -> SimulationState -> Bool
canMove usr roomnr (SimulationState s w) = elem roomnr (map exitToNr exits)
                                               where Room _ _ exits _ _ _ = (findRoom (concat s)) ((\(Agent pos _ _) -> pos) (w M.! usr))                                           

canPickup :: User -> SimulationState -> Bool
canPickup usr (SimulationState s w) = case findRoom (concat s) ((\(Agent pos _ _) -> pos) (w M.! usr)) of
                Room _ _ _ Extinguisher _ _-> True && (\(Agent _ h _) -> h == NoItem) (w M.! usr)
                _ -> False

canExtinguish :: User -> SimulationState -> Bool
canExtinguish usr (SimulationState s w) = case w M.! usr of
              Agent _ Extinguisher _ -> True && (\(Room _ _ _ _ s _) -> s == Fire) ((findRoom (concat s) ((\(Agent pos _ _) -> pos) (w M.! usr))))
              _ -> False

applyExtinguish :: User -> SimulationState -> SimulationState
applyExtinguish usr (SimulationState s w) = SimulationState (updateRoom s pos (Room pos coord exits has Normal roomWidth)) (M.insert usr (Agent pos NoItem usr) w)
                                                      where 
                                                        Room _ coord exits has roomState roomWidth = findRoom (concat s) pos
                                                        Agent pos holds urs = w M.! usr


ship1 :: ShipMap
ship1   = [[sback0]
           , [sroom01, sroom02, sroom03]
           , [scorridor0]
           , [sroom04, sroom05, sroom06]
           , [sroom07, sroom08]
          ]

sback0     = Room 1 (0,0) [ESouth 2, ESouth 3, ESouth 4]                          NoItem       Normal 3
sroom01    = Room 2 (0,1) [ENorth 1, ESouth 5]                                      NoItem       Normal 1
sroom02    = Room 3 (1,1) [ENorth 1, ESouth 5]                                      NoItem       Normal 1
sroom03    = Room 4 (2,1) [ENorth 1, ESouth 5]                                      Extinguisher Normal 1
scorridor0 = Room 5 (0,2) [ENorth 2, ENorth 3, ENorth 4, ESouth 6, ESouth 7, ESouth 8] NoItem       Normal 3
sroom04    = Room 6 (0,3) [ENorth 5, ESouth 9]                                      NoItem       Normal 1
sroom05    = Room 7 (1,3) [ENorth 5, ESouth 9]                                      NoItem       Normal 1
sroom06    = Room 8 (2,3) [ENorth 5, ESouth 10]                                     NoItem       Normal 1
sroom07    = Room 9 (0,4) [ENorth 6, ENorth 7]                                      NoItem       Normal 2
sroom08    = Room 10 (1,4) [ENorth 8]                                              NoItem       Fire   1


shipTree :: RuleTree SimulationState
shipTree = Parallel (map (\usr -> Assign usr (shipSimulation usr)) [alice, bob])

shipSimulation :: User -> RuleTree SimulationState
shipSimulation usr =  times 10 (Choice ( [ Leaf (Condition "" (canPickup usr) (Rule "Pickup" (applyPickup usr)))
                                    , Leaf (Condition "" (canExtinguish usr) (Rule "extinguish" (applyExtinguish usr)))
                                    ] ++ (map (\x -> Leaf (Condition "" (canMove usr x) (Rule (show x) (applyMove usr x)))) [1..10]))
                            )


testState = SimulationState ship1 (M.fromList [(alice,Agent 1 NoItem alice), (bob,Agent 1 NoItem bob)])


shipScore :: SimulationState -> Int
shipScore st@(SimulationState _ w) | shipNotOnFire st = 0
                                   | length (filter (\(Agent _ holds _) -> holds == Extinguisher)(M.elems w)) >0 = fireScore st
                                   | otherwise = (extScore st) + 1 + 5


extScore :: SimulationState -> Int
extScore (SimulationState s w) = minimum (map (\worker -> extDist worker (extPos)) workerCoord)
                       where workerpos = (map (\(Agent pos _ _)-> pos) (filter (\(Agent _ holds _) -> holds == NoItem)(M.elems w)))
                             coordList = map (\(Room _ coord _ _ _ _) -> coord) (concat s)
                             workerCoord = map (\pos -> coordList!!(pos-1)) workerpos
                             extDist _        []   = 0
                             extDist (px, py) exts = foldr min 10000 (map (\(x,y) -> abs (x-px) + abs (y-py)) exts)
                             extPos = map (\(Room _ coord _ _ _ _) -> coord) (filter (\(Room _ _ _ has _ _) -> has == Extinguisher)(concat s))


fireScore :: SimulationState -> Int
fireScore (SimulationState s w) = case (map (\worker -> fireDist worker (firePos)) workerCoord) of
                                                [] -> 10000
                                                x  -> minimum x
              where workerpos = map (\(Agent pos _ _) -> pos) (filter (\(Agent _ holds _) -> holds == Extinguisher)(M.elems w))
                    coordList = map (\(Room _ coord _ _ _ _) -> coord) (concat s)
                    workerCoord = map (\pos -> coordList!!(pos-1)) workerpos
                    fireDist _        []   = 0
                    fireDist (px, py) exts = foldr min 10000 (map (\(x,y) -> abs (x-px) + abs (y-py)) exts) 
                    firePos = map (\(Room _ coord _ _ _ _) -> coord) (filter (\(Room _ _ _ _ roomState _) -> roomState == Fire)(concat s))  


  --Theorems

rtEquality :: RuleTree [Int] -> [Int] -> Property
rtEquality rt s = (S.fromList $ traceS rt s) === (S.fromList $ appS rt s)
                     where
                       traceS  rt s  = tracesToLeaf (traces rt s)
                       appS    rt s  = case appRT rt s of {Just x -> x;Nothing->[]}

firstsProgress :: RuleTree Int -> Int -> Bool
firstsProgress rt s = case (firsts rt s) of
                         Nothing -> True
                         Just [] -> True
                         Just x  -> and [ruleCount rt' < ruleCount rt|(_,rt')<-x]

ruleCount :: RuleTree a -> Int
ruleCount (Seq (rt:rts)) = ruleCount rt + ruleCount (Seq rts)
ruleCount (Seq []) = 0
ruleCount (Choice (rt:rts)) = ruleCount rt + ruleCount (Choice rts)
ruleCount (Choice []) = 0
ruleCount (Parallel (rt:rts)) = ruleCount rt + ruleCount (Parallel rts)
ruleCount (Parallel [] ) = 0
ruleCount (Leaf _) = 1
ruleCount Empty = 0
ruleCount (Assign u rt) = ruleCount rt


genPar :: Gen (RuleTree [Int])
genPar = oneof [ do
                 rts <- listOf genPar
                 return $ Seq rts,
                 do
                 rts <- listOf genPar
                 return $ Choice rts,
                 do
                 rts <- listOf genPar
                 return $ Parallel rts,
                 do
                 r <- genParRule
                 return $ Leaf r,
                 return Empty,
                 do
                  u <- arbitrary
                  rt <- genPar
                  return $ Assign u rt
                 ]

genParRule :: Gen (Rule [Int])
genParRule = oneof [ do
                      e1 <- arbitrary
                      e2 <- arbitrary
                      e3 <- arbitrary
                      e4 <- arbitrary
                      e5 <- arbitrary
                      return $ Rule (show e1 ++ " " ++ show e2 ++" " ++ show e3 ++ " " ++show e4 ++ " " ++show e5) (\(s1:s2:s3:s4:s5:sx)->(e1 + s1:e2 + s2:e3 + s3:e4 + s4:e5 + s5:sx))
                    ,do
                      p <- (arbitrary :: Gen [Int]) `suchThat` (\x-> (length x) == 5)
                      r <- genParRule
                      return $ Condition (show p) (\z-> z < p) r]

genParEffect :: Gen (Int -> Int)
genParEffect = oneof [return id,
                      arbitrary]
  -- shorthands
always r = Condition "always" (\_ -> True) r
never r = Condition "never"  (\_ -> False) r
smaller n r = Condition "smaller than" (\z -> z < n) r
plus n  = Rule ("plus " ++ show n) (\z -> z + n)
minus n = Rule ("minus " ++ show n) (\z -> z - n)