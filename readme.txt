===========
Overview:
===========

This is the string diagram rewriting tool prototype, called "Box of Strings" or "Stringbox" for short.
This tool allows you to manipulate string diagrams with your mouse, applying transformation rules to prove relational properties of morphisms of monoidal categories.
You can load in a particular categorical theory, and go through a series of Definitions and Lemmas, learning about the theory and proving properties about it.
You can furthermore typset your own theory to be loaded into the program.

The tool is further developed under the ARIA safeguarded AI project and the Post-Cartesian programming PRG grant.

-- developers --
Tool concept and development:	Niels Voorneveld, Cybernetica.
Project manager and adviser: 	Pawel Sobocinski, Tallinn University of Technology
Additional features: 		Anton Osvald Kuusk, Tallinn University of Technology


===========
How to run:
===========

You can either find a build that works for your operating system, or make a build yourself.

To run existing build:
1) To run existing executable, make sure that the executable is in the same folder as the "input" folder.
2) Execute the executable
3) You can pick a file to go through it. Before picking, you can resize the window, and scroll to zoom in and out.

To make build:
1) Make sure you have haskell and cabal installed.
2) Make sure you have the complete set of files, that is: .cabal file, app folder with files, and input folder with files.
3) Navigate to folder in terminal, and type "cabal run" or "cabal run :all" to make a build.
extra) If build was succesful, you can find the executable somewhere within the "dist-newstyle" folder. You can use that (together with the "input" folder) to run the tool, without having to rebuild. Foolow instruction, to run existing build above to do so.

Troubleshooting: There may be some issues related to packages and haskell version. Feel free to change versions in the cabal file if needed to make the build.

====================
How to use the tool:
====================

There are two input schemas you can use, with different function:

I) The mouse or touchpad: is used to manipulate the string diagram according to the existing rules.
II) The keyboard: Is used to build and modify the string diagram, to make your own examples. Keyboard can only be used like this in the editor mode, which is automatically initiated upon reaching the end of a file.

Basically, as long as you use only the mouse, you are making legal/mathematically correct rewriting rules. The only exception being clicking on a preset on the left, which loads a different example.

------------------------------------
The mouse: Rewriting string diagrams
------------------------------------

Move the mouse around to investigate different elements.
Hovering over nodes in the string diagram will reveal if any rewrites are available for that node.
Hovering to the left bar allows you to look at different presets, and look through the history of string diagrams.

THE MAIN MIDDLE SCREEN (WORKBENCH)

1) Click and drag a node on the main screen to change it's location.
- Nodes may reorient themselves when possible according to the monoidal interchange rule.
- Colliding nodes will combine them, packaging them up into a composite node.
- Releasing the node will allow it to go back to a cannonical position

2) Right click a composite node on the main screen to unfold its contents.

3) Use the mouse wheel (or comparable functionality on touchpad) while hovering over a node to apply a rewrite. Available rewrites are displayed on the right

So to apply a rewrite rule, click and drag a node to combine it into a composite node matching some equation in the theory. Scroll to rewrite the content of the composite node. Then right click to release the content of the rewritten composite node. If an equation already applies to a singular node, you can immediately scroll to rewrite.

4) Click the tiny circle in the middle of a string to create an identity composite node for rewriting. Create multiple identity composite nodes and collide them to create identities of multiple wires.

There are two functionailities not yet implemented, apologies:

a) You cannot as of yet create a void composite node out of nothing, that is an identity on a monoidal unit.

b) No control over location of Units and counits when applying interchange when dragging them around.

THE LEFT HISTORY BAR

The left bar contains the goal of your current rewriting taks, and a history of the string diagrams you have rewritten.

The bar only displays 4-5 diagrams at a time. To look at the other diagrams, hover the mosue over the bar. If the mouse is at the top of the screen, it displays the top of the bar. If the mouse is at the bottom, it displays the bottom.

1) Left clicking on a morphism in the bar will replace the morphism on the main screen with that morphism.

2) Right clicking on a morphism in the bar will delete/remove it from the bar.

3) Adding to the history:
Every time you unfold a composite node on the main screen, if the string diagram on the main screen does not contain any composite nodes, and if the string diagram is monoidally different from the top morphism in the bar, the morphism will be added to the top of the bar.

-----------------------------------
The Keyboard: Typesetting a diagram
-----------------------------------

This mode automatically starts when you have gone through the whole file.

Using the keyboard, you can make crude modification to the string diagram on the main screen. If an action is not possible, nothing happens.

[Delete]      Remove the last node from the diagram
[Down-arrow]  Move the last node of the diagram one position down
[Up-arrow]    Move the last node of the diagram one position up
[Right-arrow] Add string to the bottom of the diagram
[Left-arrow]  Remove string from the bottom of the diagram
[0-9]         Change number of input wires of last node in diagram to the number pressed
[Alt]+[0-9]   Change number of output wires of last node in diagram to the number pressed

Pressing any remaining character, be it letter or symbol, will check the existing list of basic operations for one matching the symbol typed. It will add this operation. Some notes:
- Change position, number of inputs and outputs using the buttons described above.
- if multiple operations start with the same letter, one of them is selected and added. 
- the same drawing style of the operation is used.
- every node is associated a symbol, even if that symbol is not displayed. For instance, the swap operation is bound to 'x', and the bullet operations are likely bound to 'a'.
- If a symbol typed not corresponding to any existing operation, then a unit with that name is added. Note however, that no equations are specificied for newly added operations.


=====================
Writing inputs files:
=====================
The file reader is still in flux, as more features are added.
Main things that may change are:
- Addition of types of relations, requiring more options
- Parametrizing operation by numbers
- Making objects variable dependent for schema definitions
So, if you do use this tool to showcase your own examples, please keep the appropriate build.
Examples from the repository will be updated to fit new reader rewuirements.

General file reading principles:
- Spaces, lineskips and tabs are completely ignored
- Anything between two # symbols is ignored, so can be used as comment
- Arguments of functions are put in between {} brackets.
- Parsing happens by checking the next symbol not falling in the above categories. The symbol tells us what operation is being declared, and then an appropriate number of subsequent arguments dependent on the operation are read. Anything between the arguments outside the {} brackets, or between the invoking symbol and the first argument, is ignored. So if the invoking symbol is "D", you can freely write "Definition" or "Display", or even "Define(Unitality Law)" to give more information. Parsing the rest of the file continues right after the last argument.

Different functions:
I - "Import", needs to be used at the start of the file. Has one argument "I{file}"; reads an entirely different file using the name given in "file", and extracts all the rewrites from it without displaying the D, L or E options. This is to build off other theories. Imports are iterative, so only Import the last file in a chain. Repeat imports are fine. Cyclical imports should be avoided.
O - "Operation" adds an operation to the signature of operations. Has four arguments: "O{c}{s}{i}{o}"; the key character name c, the display style s, the number of input wires i, and number of output wires o.
A - "Assume"/"Axiom" adds a rewrite rule to the theory. Has three arguments "A{i}{s}{g}"; the number of input wires i for both the starting morphism and goal morphism, the starting morphism of operations s, the ending morphism of the operation g. 
D - "Define"/"Display", same as "A", but moreover puts the rewrite rule on the workbench display, so it is shown to user who can apply the rule to see what it looks like.
L - "Lemma", same as "D", except that it adds the rewrite rule after the user has been displayed on the workbench. So the user can try to prove the lemma without having access to it (Note, too many lemmas may get in the way of convenience, which is why we have the next option).
E - "Example"/"Exercise", same as "L", but the rewrite rule is never added. So the user can try and prove the rewrite rule, but will not get the rule afterwards.
S - "Schema", hase three argument "S{name}{l}{r}", the name of the schema, the list l of arguments for the schema, and the list r of possible substitutions into the schema. If r is left empty, as {}, then schema applies to all operations. Schemas cannot refer to any operations not yet added, and adding the same schema with the same arguments will overwrite the r (e.g. you can limit a schema after importing it, if it should not apply to new operations in the theory)

Defining morphisms:
Morphisms are defined using a sequence of the following: "i.c;", that is a number "i" and a character "c", separated by a dot "." and closed with a semicolon ";". The "c" is the character associated to the relevant operation, which must have been added beforehand (either in the same file or imported). The "i" is a number, which can be multiple characters but likely is not, designating how many wires are "skipped". So supposing the object at the moment is "n", and the number of input wires for operation "c" is "j", then "i.c;" is akin to composing the morphism build up to this point with "id_i x c x id_{n-i-j}". You just ensure yourself that "i+j" does not exceed "n".
When generating a morphism, some starting number of wires is used, and then for each "i.c;" in the sequence an operation is added as specified above. Nothing after the final ";" is parsed, nor anything between "c" and the ";", nor anything beyond the initial sequence of numbers in "i" before the ".".


