# OWL
OWL in agda

Copyright Gavin Mendel-Gleason, released under the GPL.

The basic idea of the code thus far is to provide semantics for OWL Full.  It is subject to certain constraints for practicallity, in particular that the modeling sets for individuals and datatypes is small (Set zero - in Agda parlance). 

The description is checked against interpretation functions.  There are example interpretation functions for a specific OWL theory provided.  To make the semantics practically more useable, it would be necessary to choose a fragment for which interpretation functions can be constructed automatically.  These could then be shown to satisfy the OWL semantics by construction.

In order to load this code, you need to d/l and install Agda.  

http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Download

The code were developed using Agda 2.4.2.2 and version 0.9 of the Standard Library.
