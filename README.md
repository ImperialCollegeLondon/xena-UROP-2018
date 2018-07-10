# xena-UROP-2018
A place to put our 2018 Xena project UROP thoughts and programs.

### Installation instructions.

0) Install Lean 3.4.1 and git, and if you're on Windows then also install a program which gives you a command line like MSYS2. Furthermore, make sure the path for your command line contains the directories where Lean and git are installed. If on your command line you can type

`$ git --version`

and 

`$ lean --version`

and not get errors, you're probably good to go. Don't forget to make sure that your VS Code is pointing to the same version of Lean! (File -> Preferences -> Settings and look in user settings) 

1) Clone the repo:

`$ git clone git@github.com:ImperialCollegeLondon/xena-UROP-2018.git`

2) Install the dependencies (currently mathlib; in the future there will be a xena repository containing more mathematics):

```
$ cd xena-UROP-2018
$ leanpkg upgrade
```

3) (optional, will take a while and will use a lot of power, but will make mathlib run *much* faster): build mathlib.

```
$ cd _target/deps/mathlib/
$ leanpkg build
```

