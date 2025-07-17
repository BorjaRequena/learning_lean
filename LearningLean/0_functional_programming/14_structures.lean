/- The first step in writing a program is usually to identify the problem domain's concepts, and
then find suitable representations for them in code. Sometimes, a domain concept is a collection
of simpler concepts. In that case, it can be convenient to group these together into a single
structure.

Defining a structure introduces a completely new type to Lean that can't be reduced to any other
type. Multiple structures might represent different concepts that nonetheless contain the same data.
For instance, a point might be represented using Cartesian or polar coordinates, each being a pair
of floating-point numbers. Defining separate structures prevents API clients from confusing one for
another.-/

-- Let's start with the example of a point in 2D space.
-- Lean has the Float type for floating-point numbers.
#check 1.2

-- We can define a Cartesian point as a pair of floating-point numbers.
structure CartesianPoint where
  x : Float
  y : Float
deriving Repr -- This line generates code to display values of type CartesianPoint

-- We can instantiate a structure providing the values for each field in curly braces.
def origin: CartesianPoint := {x := 0.0, y := 0.0}

#eval origin

-- We can also access the individual fields of a structure using the dot notation.
#eval origin.x
#eval origin.y

-- This allows us to define functions that use the fields of a structure.
def addPoints (p1 : CartesianPoint) (p2 : CartesianPoint) : CartesianPoint :=
  {x := p1.x + p2.x, y := p1.y + p2.y}

#eval addPoints origin origin

-- We can also evaluate this function with any structure that has the same fields.
#eval addPoints { x := 1.5, y := 32 } { x := -8, y := 0.2 }

-- Similarly, we can define a distance function that returns a Float
def distance (p1 : CartesianPoint) (p2 : CartesianPoint) : Float :=
  Float.sqrt ((p1.x - p2.x) ^ 2 + (p1.y - p2.y) ^ 2)

#eval distance origin { x := 1.0, y := 1.0 }

-- While we can pass these undefined points to the functions we have created, Lean can't infer
--the type on its own.
#check { x := 1.0, y := 1.0 }

-- We need a type annotation that suits the given data structure
#check ({ x := 1.0, y := 1.0 } : CartesianPoint)

/- Updating structures is an essential aspect of working with them. Since Lean is a functional
program, this means that we can't change the values of the fields of a structure after it has been
created. Instead, we can create a new structure with the updated values. More precisely, the new
structure data points to the old values except for the fields that are being updated. -/

-- Let's start with an example that zeroes out the x-coordinate of a point.
def zeroX (p : CartesianPoint) : CartesianPoint :=
  { x := 0.0, y := p.y }

#eval zeroX { x := 3.5, y := 1.2 }

-- This syntax is brittle, since changing the point structure would imply rewriting all the
-- functions that use it. Lean has the `with` syntax to help with this.
def zeroY (p : CartesianPoint) : CartesianPoint :=
  { p with y := 0.0 }

#eval zeroY { x := 3.5, y := 1.2 }

-- Remember: these functions yield a new point, they do not modify the original one.
def somePoint : CartesianPoint := { x := 5.1, y := 2.2 }
#eval somePoint
#eval zeroX somePoint
#eval somePoint
#eval zeroY somePoint
#eval somePoint

/- Under the hood, every structure has a constructor that  gathers the data to be stored in the
newly-allocated data structure. Unlike other languages like Python, it is not possible to provide
custom constructors pre-processes data or reject invalid arguments.

By default, the constructor for a given structure is called `mk`. This function can be called
directly to create a new structure, even without curly bracers. -/

-- We can inspect the constructor for our point structure
#check CartesianPoint.mk
#check (CartesianPoint.mk)

-- Notice that the constructor expects 2 arguements: x and y.
#eval CartesianPoint.mk 1.0 1.0
#check CartesianPoint.mk 1.0 1.0

-- The constructor name can be overriden with a double colon syntax
structure PolarPoint where
  point ::
  r : Float
  θ : Float
  deriving Repr

#check PolarPoint.point
#check (PolarPoint.point)

-- In addition to the constructor, accessor functions are also defined for each
-- field of the structure with the same name as the field.
#check PolarPoint.r
#check (PolarPoint.r)
#check PolarPoint.θ
#check (PolarPoint.θ)

-- The accessor notation of `target.f arg1 arg2` can be used if `target` has a type
-- with a function `f`. For example, with String:
#eval "Some string".length
#eval String.length "Some string"

#eval "My cat".append " is black"
#eval String.append "My cat" " is black"

-- Mastering this allows us to write compact code. For example, we can define a
-- cartesianPoint function to modify both vlaues through a function
def CartesianPoint.applyBoth (f : Float → Float) (p : CartesianPoint) : CartesianPoint :=
  {x := f p.x, y := f p.y}

-- Here, even though the point argument is the second, we can call point.applyBoth because THE
-- TARGET of the accessor notation is USED AS THE FIRST ARGUMENT WHERE THE TYPE MATCHES, not
-- necessarily the first argument.
#eval somePoint
#eval somePoint.applyBoth (fun x ↦ x + 1)
#eval somePoint.applyBoth Float.floor

/- EXERCISES
1. Define a structure named RectangularPrism that contains the height, width, and depth of a
rectangular prism, each as a Float.
2. Define a function named volume : RectangularPrism → Float that computes the volume of a
rectangular prism.
3. Define a structure named Segment that represents a line segment by its endpoints, and define
a function length : Segment → Float that computes the length of a line segment. Segment should have
at most two fields.
4. Which names are introduced by the declaration of RectangularPrism?
5. Which names are introduced by the following declarations of Hamster and Book? What are their types?

structure Hamster where
  name : String
  fluffy : Bool

structure Book where
  makeBook ::
  title : String
  author : String
  price : Float
  -/

-- 1. Define the RectangularPrism structure
structure RectangularPrism where
  height : Float
  width : Float
  depth : Float

-- 2. Define the volume function
def volume (r : RectangularPrism) : Float :=
  r.height * r.width * r.depth

-- 3. Define the Segment structure and a length function
structure Segment where
  point1 : CartesianPoint
  point2 : CartesianPoint

def length (s : Segment) : Float :=
  distance s.point1 s.point2  -- We can use the distance function we defined earlier

#eval length { point1 := { x := 0.0, y := 0.0 }, point2 := { x := 1.0, y := 1.0 } }

-- 4. Which names re introduced by the declaration of RectangularPrism?
-- Don't fully understand the question tbh. The names would be the constructor and the accessors?
#check RectangularPrism.height
#check RectangularPrism.width
#check RectangularPrism.depth

-- 5. Which names are introduced by the declaration of Hamster and Book? What are their types?
-- Same as above but for those structures
