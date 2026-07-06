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

If you use Linux or Windows, you might want to try the precompiled binaries. If they do not work, you will need to compile yourself using Haskell.

To run existing build:
1) Find the Linux or Windows binary in the main folder.
2) Run it, either by double clicking, or by navigating to it in a terminal and typing the name of the file.
2b) In Windows, you might have to get a version of GLUT. A version is stored in the "freeGLUT" subfolder. Move it either next to the executable, or to some place in the system path. You can also try to compile a version of GLUT youself.
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

Parts of this may be outdated. Please find the quick "guide" in html format, in the "guide" subfolder, for easier reading and videos of how to use the tool.

There are two modes: rewrite mode and edit mode.

I) Rewrite Mode: Use mouse or touchpad to manipulate the string diagram according to the existing rules. If scrolling is an issue, you can use the up & down arrows instead.
II) Edit Mode: Is used to build and modify the string diagram, to make your own definitions and lemmas. 

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

3) Use the mouse wheel (or comparable functionality on touchpad) while hovering over a node to cycle through applicable rewrites. Available rewrites are displayed on the right

So to apply a rewrite rule, click and drag a node to combine it into a composite node matching some equation in the theory. Scroll to rewrite the content of the composite node. Then right click to release the content of the rewritten composite node. If an equation already applies to a singular node, you can immediately scroll to rewrite.

4) Click the tiny circle in the middle of a string to create an identity composite node for rewriting. Create multiple identity composite nodes and collide them to create identities of multiple wires.

5) Click anywhere else in the diagram to create an empty box.

THE LEFT HISTORY BAR

The left bar contains the goal of your current rewriting task, and a history of the string diagrams you have rewritten.

The bar only displays 4-5 diagrams at a time. 

1) Scroll when hovering over the left bar to quickly change between states. 

2) Click on the previous or next state to animate transitioning between them.

3) Adding to the history:
Every time you unfold a composite node on the main screen, if the string diagram on the main screen does not contain any composite nodes, and if the string diagram is monoidally different from the top morphism in the bar, the morphism will be added to the top of the bar.

-----------------------------------
The Keyboard: Typesetting a diagram
-----------------------------------

If you reach the end of the file, you will open the in-tool editor. This allows you to add new operations, axioms and lemmas on the fly, and these will be added to the file (the additions can be edited or removed by opening the file with a text editor, see next part for more typesetting details).

Modifying the displayed diagram: Scroll to add or remove strings at the bottom. Click operations on the left, or type their corresponding letter on the keyboard, to add the operation to the diagram. Nothing will happen if there are not enough strings available. Click and drag operations to change their position, they will jump strings, unlike in rewrite mode (you may have to add more strings at the bottom to move an operation around another one). Right-click an operation to remove it from the diagram, this may fail if this leaves insufficient strings for the operations on the right.

Specifying rewrites: Click on the options on the right to shift between definition (axiom) and lemma. When you have finished typesetting the initial state of the rewrite, press next to go to the goal state. This will copy the current state, which you can now edit. If the goal state is kept equal to the starting state, the string diagram will be added as a Show-type.

Adding operations: If you type a character on the keyboard not bound to any existing operation, you intiate adding a new operation. Specify by typing two digits the number of input strings and output strings respectively.

The above only gives a crude but quick way of typesetting a theory, more details would need to be typed by hand. To create a new theory, create an empty text file and load it in.


=====================
Writing inputs files:
=====================

See the guide for more details.

