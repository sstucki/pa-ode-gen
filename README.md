The Preferential Attachment ODE Generator
=========================================

*pa-ode-gen*, the *P*referential *A*ttachment *ODE* *Gen*erator, is a
small, proof-of-concept tool for generating ODEs describing the time
evolution of arbitrary moments of star-counting functions in
preferential attachment networks.


How to get started
------------------

 1. Odds is written in Scala, which runs on the JVM.  So for starters,
    you'll need an up-to-date [JRE/JDK](http://openjdk.java.net/).  If
    you're on a Debian/Ubuntu system, this should do the trick:

        $ sudo apt-get install openjdk-7-jre

 2. Get an up-to-date [Scala distribution](http://www.scala-lang.org/).

 3. Clone the [GitHub repository](https://github.com/sstucki/pa-ode-gen/):

        $ git clone https://github.com/sstucki/pa-ode-gen.git

 4. Run `./ode-gen -h` to get basic instructions on how to run the
    tool.


How to run it
-------------

*pa-ode-gen* has various output formatting options so one can
 1. generate code to solve the ODEs in
    [Matlab](http://ch.mathworks.com/products/matlab/) or
    [GNU/Octave](https://www.gnu.org/software/octave/),
 2. generate pretty pictures of various graph motifs using
    [Graphviz](http://www.graphviz.org/),
 3. generate TeX for the ODEs.

For example, running

    $ ./ode-gen 3 2 odes.m

will generate a Matlab/Octave file called `odes.m` containing the
necessary function for computing the time evolution of the 2nd-order
moment of a 3-star, as well as some instructions on how to perform the
computation (i.e. specify rates, time steps, etc).

Similarly, to generate the ODEs in TeX, just run

    $ ./ode-gen 3 1 gluings.tex

You can also generate a
[DOT](http://en.wikipedia.org/wiki/DOT_%28graph_description_language%29)
file for visualizing a all the graph motifs necessary to compute the
mean evolution of the 3-star by running

    $ ./ode-gen 3 1 gluings.dot

This will generate a single DOT file named `gluings.dot` with four
graph definitions (one per gluing) that you can process with Graphviz
to generate a PDF like so:

    $ dot gluings.dot | gvpack -array_6 | neato -Tpdf -n2 -o gluings.pdf

If you just want to visualize the motifs, you can use e.g.

    $ ./ode-gen -d 3 1 | dot | gvpack | neato -Tx11

Here the `-d` flag tells the generator to produce DOT output directly
to standard out (there's no file name so it can't infer the format).

For a summary of all format options, run

    $./ode-gen -h


More documentation
------------------

We're working on it...


Source code
-----------

Visit [pa-ode-gen](https://github.com/sstucki/pa-ode-gen/) on GitHub.
