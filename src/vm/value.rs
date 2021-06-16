use super::Chunk;
use std::{alloc, cell::RefCell, fmt, ptr::NonNull};

/// The value type of the virtual machine
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Value {
    /// Numeric value: `12300`, `-1.23004`, etc
    Number(f64),
    /// `nil`
    Nil,
    /// `true` or `false`
    Bool(bool),
    /// Any heap allocated value
    Object(Object),
}

impl Value {
    /// Returns `true` if this `Value` is `false` or `false` equivalent.
    pub fn is_falsey(&self) -> bool {
        match self {
            Value::Nil => true,
            Value::Bool(b) => !*b,
            _ => false,
        }
    }

    /// Return `true` if this `Value` is an `Object` of the specific type.
    pub fn is_object_type<O: ConcreteObject>(&self) -> bool {
        match self {
            Value::Object(o) => o.is::<O>(),
            _ => false,
        }
    }

    /// Return a reference to a concrete object, if this `Value` is an `Object`
    /// of that type.
    pub fn to_object_type<O: ConcreteObject>(&self) -> Option<&O> {
        match self {
            Value::Object(o) => o.read(),
            _ => None,
        }
    }

    /// The statically known type of the value
    pub fn type_str(&self) -> &'static str {
        match self {
            Value::Bool(_) => "boolean",
            Value::Number(_) => "number",
            Value::Object(obj) => obj.read_base().obj_type.to_str(),
            Value::Nil => "null",
        }
    }
}

impl From<f64> for Value {
    fn from(src: f64) -> Self {
        Value::Number(src)
    }
}

impl From<bool> for Value {
    fn from(src: bool) -> Self {
        Value::Bool(src)
    }
}

impl From<Object> for Value {
    fn from(src: Object) -> Self {
        Value::Object(src)
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Number(n) => <f64 as fmt::Display>::fmt(n, f),
            Value::Nil => write!(f, "nil"),
            Value::Bool(b) => <bool as fmt::Display>::fmt(b, f),
            Value::Object(o) => <Object as fmt::Display>::fmt(o, f),
        }
    }
}

/// A memory region that contains `Value`s, separate from the stack.
#[derive(Debug)]
pub struct Heap(RefCell<HeapInner>);

#[derive(Debug)]
struct HeapInner {
    /// The head of a linked list containing all `Object`s allocated by this
    /// `Heap`.
    pub last_allocated: Object,
}

impl Heap {
    /// Create a new, empty `Heap`.
    pub fn new() -> Self {
        Heap(RefCell::new(HeapInner::new()))
    }

    /// Reset the contents of the `Heap`, all `Objects` will be invalid after
    /// calling this.
    ///
    /// # Safety
    ///
    /// The safety requirements detailed in the `deallocate_object`
    /// documentation are applied for every `Object` allocated by this `Heap`.
    /// In essence, none of the surviving `Object`s (specifically allocated by
    /// this `Heap`) may be used or read from in any way.
    pub unsafe fn clear(&self) {
        let mut inner = self.0.borrow_mut();

        inner.clear();
    }

    /// Allocate a new `StringObject` in the `Heap`.
    pub fn allocate_string(&self, s: impl Into<String>) -> Object {
        let mut inner = self.0.borrow_mut();

        inner.allocate_string(s)
    }
}

impl HeapInner {
    /// Create a new, empty `Heap`.
    fn new() -> Self {
        HeapInner {
            last_allocated: Object::dangling(),
        }
    }

    /// Reset the contents of the `Heap`, all `Objects` will be invalid after
    /// calling this.
    ///
    /// # Safety
    ///
    /// The safety requirements detailed in the `deallocate_object`
    /// documentation are applied for every `Object` allocated by this `Heap`.
    /// In essence, none of the surviving `Object`s (specifically allocated by
    /// this `Heap`) may be used or read from in any way.
    pub unsafe fn clear(&mut self) {
        let mut current = self.last_allocated;
        // Set the `last_allocated` to dangling before looping through so that any
        // errors/panics will only leak memory, not leave deallocated `Object`s in the
        // list.
        self.last_allocated = Object::dangling();

        while current.0 != NonNull::dangling() {
            // # Safety
            //
            // 1. `current_ptr.read`
            //   - ptr is valid for reads, aligned, and initialized; all by construction in
            //     `allocate_with`
            // 2. `self.deallocate_object`
            //   - The requirements on the lifetime of all copies of the `current` `Object`
            //     must be satisfied by the caller of this function. See the safety
            //     documentation of this function for more details.
            unsafe {
                let next = current.0.as_ptr().read().next_obj;
                self.deallocate_object(current);
                current = next;
            }
        }
    }

    #[allow(clippy::mut_from_ref)]
    fn allocate_with<'h, 'o, T: ConcreteObject>(&'h self, f: impl FnOnce() -> T) -> &'o mut T {
        let layout = alloc::Layout::new::<T>();
        if layout.size() == 0 {
            panic!("Cannot allocate zero-sized value!");
        }

        // # Safety
        //
        // 1. `alloc::alloc`
        //   - value is non-zero in size
        //   - the allocated memory is immediately overwritten, so uninitialized memory
        //     does not leak
        let ptr = unsafe { alloc::alloc(layout) }.cast::<T>();

        if ptr.is_null() {
            alloc::handle_alloc_error(layout)
        }

        // # Safety
        //
        // 1. `ptr.write`
        //   - ptr is valid: non-null, dereferenceable (possibly not relevant for this
        //     case)
        //   - ptr is properly aligned because of Layout
        //
        // 2. `ptr.as_mut`
        //   - ptr is properly aligned because of Layout
        //   - ptr is dereferenceable: the value T was allocated as a whole object
        //      - a counter example would be attempting to use a ptr to the first of two
        //        allocated objects that make up the whole, assuming that the
        //        allocations are adjacent
        //   - ptr points to a initialized instance of T (due to previous `ptr.write`)
        //   - ptr obeys aliasing rules, as the resulting reference will be unique
        unsafe {
            ptr.write(f());
            ptr.as_mut().unwrap()
        }
    }

    fn allocate_object_with<T: ConcreteObject>(&mut self, f: impl FnOnce() -> T) -> Object {
        let object = self.allocate_with(f);
        let object = T::upcast(object);
        self.last_allocated = object;
        object
    }

    /// Allocate a new `StringObject` in the `Heap`.
    pub fn allocate_string(&mut self, s: impl Into<String>) -> Object {
        self.allocate_object_with({
            let last_allocated = self.last_allocated;
            move || StringObject {
                base: ObjectBase {
                    obj_type: ObjectType::String,
                    next_obj: last_allocated,
                },
                value: s.into().into_boxed_str(),
            }
        })
    }

    /// Allocate a new `FunctionObject` in the `Heap`.
    ///
    /// # Panics
    /// This function panics if the given `name` is not a reference to a
    /// `StringObject`.
    pub fn allocate_function(&mut self, name: Object, arity: u16, chunk: Chunk) -> Object {
        assert!(name.is::<StringObject>());

        self.allocate_object_with({
            let last_allocated = self.last_allocated;
            move || FunctionObject {
                base: ObjectBase {
                    obj_type: ObjectType::Function,
                    next_obj: last_allocated,
                },
                name,
                arity,
                chunk,
            }
        })
    }

    /// Deallocate the memory backing the given `Object`.
    ///
    /// # Safety
    /// Each `Object` is a wrapper around a non-null, mutable pointer which can
    /// be cloned and shared. This presents an issue when it comes to
    /// deallocating the `Object`, as other copies may point to the same
    /// storage. This can end up in a "use after free" situation.
    ///
    /// It is the responsibility of the caller to ensure that either:
    ///   - the given `Object` is the only copy pointing to the memory
    ///   - OR all other copies will never be read from again
    unsafe fn deallocate_object(&self, object: Object) {
        let (ptr, layout) = match object.read_base().obj_type {
            ObjectType::String => {
                let concrete_ptr = object.0.cast::<StringObject>().as_ptr();

                // # Safety
                //
                // 1. `ptr.drop_in_place`
                //   - ptr is valid for both read and write by construction in `allocate_with`
                //   - ptr is aligned by construction in `allocate_with`
                //   - StringObject behind ptr is valid for dropping, the inner string data must
                //     be deallocated.
                unsafe { concrete_ptr.drop_in_place() };

                (
                    concrete_ptr.cast::<u8>(),
                    alloc::Layout::new::<StringObject>(),
                )
            },
            ObjectType::Function => {
                let concrete_ptr = object.0.cast::<FunctionObject>().as_ptr();

                // The `name: Object` will be dropped, but this will not deallocate the memory
                // back the `StringObject` it points to. The garbage collection
                // (when implemented) will handle cleanup of the object.
                //
                // # Safety
                //
                // 1. `ptr.drop_in_place`
                //   - ptr is valid for both read and write by construction in `allocate_with`
                //   - ptr is aligned by construction in `allocate_with`
                //   - FunctionObject behind ptr is valid for dropping, the chunk data must be
                //     deallocated
                unsafe { concrete_ptr.drop_in_place() };

                (
                    concrete_ptr.cast::<u8>(),
                    alloc::Layout::new::<FunctionObject>(),
                )
            },
        };

        // # Safety
        //
        // 1. `alloc::dealloc`
        //   - ptr was allocated using the `alloc::alloc` function in `allocate_with`
        //     (above)
        //   - layout is the same, ensured using the `ObjectType` tag to recall the
        //     original allocating type
        unsafe { alloc::dealloc(ptr, layout) }
    }
}

impl Default for Heap {
    fn default() -> Self {
        Heap::new()
    }
}

/// On `drop` deallocate all memory that was used by this `Heap`.
///
/// # Safety
///
/// The safety requirements detailed in the `deallocate_object`
/// documentation are applied for every `Object` allocated by this `Heap`.
/// In essence, none of the surviving `Object`s (specifically allocated by
/// this `Heap`) may be used or read from in any way.
impl Drop for HeapInner {
    fn drop(&mut self) {
        // # Safety
        //
        // 1. `self.clear`
        //   - None of the safety requirements are discharged, only the doc-comment on
        //     this `Drop` impl serves to alert users what the requirements of using
        //     this are.
        //   - The only reason this is added is to reduce memory leakage in the simplest
        //     case.
        unsafe { self.clear() }
    }
}

/// An opaque object reference.
#[derive(Debug, Copy, Clone)]
pub struct Object(NonNull<ObjectBase>);

impl Object {
    fn dangling() -> Self {
        Object(NonNull::dangling())
    }

    fn read_base(&self) -> &ObjectBase {
        // # Safety
        //
        // 1. `ptr.as_ref`
        //   - ptr is properly aligned, dereferenceable, & initialized, ensured by
        //     `allocate_with`
        //   - aliasing rules are obeyed, as it is currently impossible to obtain a
        //     mutable reference to the object
        unsafe { self.0.as_ref() }
    }

    /// Returns some reference to the value if it is of type T, or None if it
    /// isn't.
    pub fn read<T: ConcreteObject>(&self) -> Option<&T> {
        self.read_base().downcast_ref::<T>()
    }

    /// Write to the formatter the representation that would normally be
    /// encapsulated in the `fmt::Display` trait.
    pub fn display_fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let self_base = self.read_base();

        match self_base.obj_type {
            ObjectType::String => <StringObject as fmt::Display>::fmt(
                self_base.downcast_ref::<StringObject>().unwrap(),
                f,
            ),
            ObjectType::Function => <FunctionObject as fmt::Display>::fmt(
                self_base.downcast_ref::<FunctionObject>().unwrap(),
                f,
            ),
        }
    }

    /// Return `true` if this Object is equivalent to the given Object.
    pub fn partial_eq(&self, other: &Self) -> bool {
        let self_base = self.read_base();
        let other_base = other.read_base();

        match (self_base.obj_type, other_base.obj_type) {
            (ObjectType::String, ObjectType::String) => <StringObject as PartialEq>::eq(
                self_base.downcast_ref::<StringObject>().unwrap(),
                other_base.downcast_ref::<StringObject>().unwrap(),
            ),
            (ObjectType::Function, ObjectType::Function) => <FunctionObject as PartialEq>::eq(
                self_base.downcast_ref::<FunctionObject>().unwrap(),
                other_base.downcast_ref::<FunctionObject>().unwrap(),
            ),
            _ => false,
        }
    }

    /// Return `true` if this Object is a reference to the `T` super-type.
    pub fn is<T: ConcreteObject>(&self) -> bool {
        self.read_base().obj_type == T::TYPE
    }

    /// Return a static string which roughly represent the type of the object
    pub(crate) fn type_str(&self) -> &'static str {
        self.read_base().obj_type.to_str()
    }
}

impl PartialEq for Object {
    fn eq(&self, other: &Self) -> bool {
        self.partial_eq(other)
    }
}

impl fmt::Display for Object {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.display_fmt(f)
    }
}

/// This trait encompasses the behavior of all concrete object types, i.e. all
/// Objects that do not require more casting to be functional.
pub trait ConcreteObject: fmt::Display + PartialEq {
    /// The `ObjectType` of the `ConcreteObject`.
    const TYPE: ObjectType;

    /// Take a mutable pointer to a `ConcreteObject` value, and produce an
    /// `Object` that references that initial value
    fn upcast(own: *mut Self) -> Object {
        Object(NonNull::new(own.cast::<ObjectBase>()).unwrap())
    }
}

/// The type of an Object
#[derive(Debug, Copy, Clone, PartialEq, Hash)]
pub enum ObjectType {
    /// The type of an Object that contains immutable text data
    String,
    /// The type of an Object that represents a source code-defined function
    Function,
}

impl ObjectType {
    fn to_str(&self) -> &'static str {
        match self {
            ObjectType::String => "string",
            ObjectType::Function => "function",
        }
    }
}

/// The base fields of all Objects
#[derive(Debug, Clone)]
#[repr(C)]
pub struct ObjectBase {
    /// The type of Object that this base is a part of
    pub obj_type: ObjectType,
    /// The last allocated `Object` prior to this one, part of the linked list
    /// containing all `Object`s allocated by the same `Heap`.
    pub next_obj: Object,
}

impl ObjectBase {
    fn downcast_ref<T: ConcreteObject>(&self) -> Option<&T> {
        if self.obj_type == T::TYPE {
            // # Safety
            //
            // 1. `ptr.as_ref`
            //   - ptr is non-null, aligned, dereferenceable, initialized: all by
            //     construction in `allocate_with`
            //   - the returned reference obeys the aliasing rules, so long as the `&self:
            //     &ObjectBase` parameter does as well
            Some(unsafe { (self as *const Self).cast::<T>().as_ref().unwrap() })
        } else {
            None
        }
    }
}

/// An immutable String object
#[derive(Debug)]
#[repr(C)]
pub struct StringObject {
    /// The base fields of the `StringObject`.
    pub base: ObjectBase,
    /// The string content
    pub value: Box<str>,
}

impl ConcreteObject for StringObject {
    const TYPE: ObjectType = ObjectType::String;
}

impl fmt::Display for StringObject {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <str as fmt::Display>::fmt(&*self.value, f)
    }
}

impl PartialEq for StringObject {
    fn eq(&self, other: &Self) -> bool {
        (*self.value).eq(&*other.value)
    }
}

impl PartialEq<str> for StringObject {
    fn eq(&self, other: &str) -> bool {
        self.value.as_ref().eq(other)
    }
}

/// A function defined in the lox source code
#[derive(Debug)]
#[repr(C)]
pub struct FunctionObject {
    /// The base fields of the `FunctionObject`.
    pub base: ObjectBase,
    /// The number of function arguments
    pub arity: u16,
    /// The bytecode of the function
    pub chunk: Chunk,
    /// The function name
    pub name: Object,
}

impl ConcreteObject for FunctionObject {
    const TYPE: ObjectType = ObjectType::Function;
}

impl fmt::Display for FunctionObject {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<fn {}>", self.name)
    }
}

impl PartialEq for FunctionObject {
    fn eq(&self, other: &Self) -> bool {
        self.arity.eq(&other.arity) && self.name.eq(&other.name) && self.chunk.eq(&other.chunk)
    }
}
