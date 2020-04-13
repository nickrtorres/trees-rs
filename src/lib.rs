#![warn(clippy::all, clippy::pedantic)]
//! A *complete* implementation of the `BinaryTree` sample given in
//! *Programming Rust* by Jim Blandy and Jason Orendorff.
use std::cmp::{Ord, Ordering};
use std::default::Default;
use std::fmt;
use std::iter::FromIterator;

/// Jim Blandy and Jason Orendorff implement this as an enum with two variants:
/// `Empty` and `NonEmpty`. While this works, it is very similar to Rust's
/// built in [`Option` type][wheel].
///
/// [wheel]: <https://rust-unofficial.github.io/too-many-lists/second-option.html>
#[derive(PartialEq, Debug)]
pub struct BinaryTree<T> {
    root: Option<Box<TreeNode<T>>>,
}

impl<T> Default for BinaryTree<T> {
    fn default() -> Self {
        BinaryTree { root: None }
    }
}

#[cfg(test)]
impl<T: Ord + fmt::Debug> fmt::Display for BinaryTree<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        return self.write_in_order(f);
    }
}

impl<T: Ord + fmt::Debug> BinaryTree<T> {
    #[cfg(test)]
    fn write_in_order(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match &self.root {
            None => {}
            Some(t) => {
                t.left.write_in_order(f)?;
                write!(f, "{:?}", t.element)?;
                t.right.write_in_order(f)?;
            }
        }

        Ok(())
    }

    /// Gets the number of elements from the current element down
    pub fn size(&self) -> usize {
        self.root
            .as_ref()
            .map_or(0, |b| 1 + b.right.size() + b.left.size())
    }

    /// Gets a reference to the root value.
    ///
    /// Returns `None` if the tree is `BinaryTree::Empty`
    pub fn first<'a>(&'a self) -> Option<&'a T> {
        self.root.as_ref().map(|b| &b.element)
    }

    /// Adds `value` to the tree
    ///
    /// TODO: handle the case where `value` is already in the tree.
    pub fn add(&mut self, value: T) {
        match self.root {
            None => {
                self.root = Some(Box::new(TreeNode {
                    element: value,
                    left: BinaryTree { root: None },
                    right: BinaryTree { root: None },
                }))
            }
            Some(ref mut b) => match Ord::cmp(&b.element, &value) {
                Ordering::Less => b.right.add(value),
                Ordering::Greater => b.left.add(value),
                Ordering::Equal => unimplemented!(),
            },
        };
    }

    /// Determines if `value` is present in the tree
    pub fn contains(&self, value: &T) -> bool {
        self.get(value).is_some()
    }

    /// Gets a reference to `value` in the tree or `None` if `value` doesn't
    /// exist in the tree
    pub fn get<'a>(&'a self, value: &T) -> Option<&'a T> {
        self.root
            .as_ref()
            .and_then(|b| match Ord::cmp(&b.element, value) {
                Ordering::Less => b.right.get(value),
                Ordering::Greater => b.left.get(value),
                Ordering::Equal => Some(&b.element),
            })
    }

    /// Returns the smallest (leftmost) element in the tree
    pub fn min(&self) -> Option<&T> {
        self.root.as_ref().and_then(|b| match b.left.root {
            None => Some(&b.element),
            Some(ref l) => l.left.min(),
        })
    }

    pub fn max(&self) -> Option<&T> {
        self.root.as_ref().and_then(|b| match b.right.root {
            None => Some(&b.element),
            Some(ref l) => l.right.max(),
        })
    }
}

/*
pub struct Iter<'a, T> {
    tree: &'a BinaryTree,
    at: usize,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    /// Performs an in order traversal of `tree`
    fn next(&mut self) -> Option<Self::Item> {}
}

impl<'a, T: Ord> IntoIterator<T> for &'a BinaryTree<T> {
    type Item = &'a T;
    type IntoIter = Iter;

    fn into_iter(self) -> Self::IntoIter {
        Iter { tree: &self, at: 0 }
    }
}
*/

impl<T: Ord + fmt::Debug> FromIterator<T> for BinaryTree<T> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let mut tree: BinaryTree<T> = Default::default();
        for e in iter {
            tree.add(e);
        }

        tree
    }
}

#[derive(PartialEq, Debug)]
pub struct TreeNode<T> {
    element: T,
    left: BinaryTree<T>,
    right: BinaryTree<T>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_can_store_n_elements() {
        let mut tree: BinaryTree<u32> = Default::default();

        tree.add(1);
        tree.add(2);
        tree.add(3);

        assert_eq!(3, tree.size());
        assert_eq!(Some(&1), tree.first());
    }

    #[test]
    fn it_can_find_elements_in_the_tree() {
        let mut tree: BinaryTree<u32> = Default::default();

        tree.add(1);
        tree.add(2);
        tree.add(3);
        tree.add(4);
        tree.add(5);
        tree.add(6);
        tree.add(7);

        assert!(tree.contains(&4));
    }

    #[test]
    fn it_can_retrieve_elements_from_the_tree() {
        let mut tree: BinaryTree<u32> = Default::default();

        tree.add(1);
        tree.add(2);
        tree.add(3);
        tree.add(4);
        tree.add(5);
        tree.add(6);
        tree.add(7);

        assert_eq!(Some(&4), tree.get(&4));
    }

    #[test]
    fn it_can_build_from_an_iterator() {
        let tree: BinaryTree<u32> = vec![1, 2, 3, 4].iter().cloned().collect();
        assert_eq!(4, tree.size());
        assert!(tree.contains(&1));
        assert!(tree.contains(&2));
        assert!(tree.contains(&3));
        assert!(tree.contains(&4));
    }

    #[test]
    fn it_can_find_the_min() {
        let mut tree: BinaryTree<u32> = Default::default();

        tree.add(7);
        tree.add(6);
        tree.add(5);
        tree.add(4);
        tree.add(3);
        tree.add(2);
        tree.add(1);

        assert_eq!(Some(&1), tree.min());
    }

    #[test]
    fn it_can_find_the_max() {
        let mut tree: BinaryTree<u32> = Default::default();

        tree.add(8);
        tree.add(1);
        tree.add(2);
        tree.add(3);
        tree.add(4);
        tree.add(5);
        tree.add(6);
        tree.add(7);

        assert_eq!(Some(&8), tree.max());
    }

    /* TODO
    #[test]
    fn it_can_turn_into_an_iterator() {
        let mut tree: BinaryTree<u32> = Default::default();

        tree.add(1);
        tree.add(2);
        tree.add(3);
        tree.add(4);

        assert_eq!(vec![1, 2, 3, 4], tree.iter().collect());
    }
    */
}
