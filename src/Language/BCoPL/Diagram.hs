module Language.BCoPL.Diagram (
  -- * Types
    Diagram (..)
  -- * Pretty Printer
  , ppr
  , textDiag
  -- * Renderer for a diagram
  , renderDiagram
  ) where

import Data.Tree (Tree(..))
import Text.PrettyPrint.Boxes (Box,(//),hsep,bottom,cols,text,moveRight,render)

data Diagram = Diagram {leading,judgement,trailing :: Int, diagram :: Box}

-- | Pretty printer for a derivation tree
ppr :: (Show a) => Tree (String,a) -> Diagram
ppr (Node (rn,j) ts) = case pprs ts of
  Diagram tlead tjudge ttrail tdia
    -> Diagram dlead djudge dtrail ddia
       where
         (blead,bjudge,btrail,bdia) = (0,cols bdia,0,text (show j))
         bdia'  = moveRight blead' bdia
         (tlead',blead') = if tent > bent then (tlead,blead+(tent-bent)`div`2)
                           else (tlead+(bent-tent)`div`2,blead)
         (tent,bent) = (2*tlead+tjudge,2*blead+bjudge)
         tdia'  = moveRight (tlead' - tlead) tdia
         mlead' = tlead' `min` blead'
         mdia   = text $ replicate (tjudge `max` bjudge) '-' ++ "(" ++ rn ++ ")"
         mdia'  = moveRight (tlead' `min` blead') mdia
         ddia   = tdia' // mdia' // bdia'
         dlead  = blead'
         djudge = cols bdia
         dtrail = cols ddia - dlead - djudge

-- | Pretty printer for a derivation forest
pprs :: (Show a) => [Tree (String,a)] -> Diagram
pprs [] = Diagram 0 0 0 (text "")
pprs ts = Diagram dlead djudge dtrail ddia
  where
    bs  = map ppr ts
    dlead  = leading $ head bs
    djudge = cols ddia - dlead - dtrail
    dtrail = trailing $ last bs
    ddia   = hsep 3 bottom $ map diagram bs

-- | Render diagram
renderDiagram :: Diagram -> String
renderDiagram = render . diagram

-- | Text diagram
textDiag :: String -> Diagram
textDiag txt = Diagram { leading = 0, judgement = length txt, trailing = 0
                       , diagram = text txt
                       }
