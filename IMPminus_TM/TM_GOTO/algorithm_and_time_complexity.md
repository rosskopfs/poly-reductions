# Reduction algorithm

###### Multitape-TM -> GOTO program on list

The reduced GOTO program works on lists, and looks roughly like this:

```
M:	IF q = F GOTO M_end;
	read_chars = Index tapes head_positions
	...
	IF q = q_i AND read_chars = cs THEN GOTO M_i_cs
	...
...
M_i_cs: modify tapes
		modify head_positions
		GOTO M
...
M_end: HALT
```

The runtime of the reduced program should be in polynomial time with respect to the runtime of the TM. Following is a simple derivation of the time complexity.

### A simple derivation of the time complexity

#### Symbols

- $k$: number of tapes in the TM
- $\Gamma$: tape character set of the TM
- $Q$: state set of the TM
- $t$: runtime of the TM

#### Idea

1. Length of block M: $\mathcal{O}(|Q| \cdot |\Gamma|^k)$

   - Important is how many `IF q=_ AND read_chars=_ THEN GOTO _`'s there are
   - That's equal to the number of possible values of `q` times that of `read_chars`
   - The number of possible values of `q` equals $|Q|$
   - The number of possible values of `read_chars` equals $|\Gamma|^k$

2. Length of each block M_i_cs: $\mathcal{O}(k)$

   - `i` is the index of the current state, and `cs` is the list of characters on each tape at the positions where the heads currently point at
   - Modification to one tape (of course at only one position, as it is in the TM) takes 1 step
   - In total, `modify tapes` takes k steps
   - Modification to the head positions of each tape takes k steps as well
   - The length of one such block is in $\mathcal{O}(k)$

3. Total runtime: $\mathcal{O}(t \cdot (|Q| \cdot |\Gamma|^k + k)) = \mathcal{O}(t)$

   - The program is executed sequentially within each blocks labelled above, hence the runtime within each block won't exceed its length

   - Each transition in the TM corresponds to the execution of a part of the `M` block and at most one `M_i_cs` block

     