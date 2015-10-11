% Lab 1 in Logic in Computer Science course
% Authors:
%           Lucas Ljungberg <lucaslj@kth.se>
%           Anton Ronsjö    <ronsjo@kth.se>
%


verify(InputFileName) :-
    see(InputFileName),
    writeln(InputFileName),
    read(Prems),
    read(Proof),
    process(Prems),
    process(Proof),
    %% read(Goal),
    %% read(Proof),
    seen.
    %valid_proof(Prems, Goal, Proof).

process(end-of-file) :- !.
process(Data) :- 
    writeln(Data).