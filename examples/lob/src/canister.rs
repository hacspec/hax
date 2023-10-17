use candid::CandidType;
use candid::Principal;
use ic_cdk::caller;
use ic_cdk_macros::{export_candid, init, query, update};
use std::cell::RefCell;

use crate::{Match, Order, OrderBook};

thread_local! {
    static ORDER_ADMIN: RefCell<Option<Principal>> = RefCell::default();
    static ORDER_BOOK: RefCell<Option<OrderBook>> = RefCell::default();
}

#[init]
fn init(order_admin: Option<Principal>) {
    ORDER_ADMIN.with(|oa| {
        *oa.borrow_mut() = order_admin;
    });
    ORDER_BOOK.with(|ob| {
        ob.borrow_mut().replace(OrderBook::new());
    });
}

#[update]
pub fn add_order(order: Order) -> Vec<Match> {
    assert!(order.quantity > 0, "Order quantity must be positive");
    ORDER_ADMIN.with(|oa| {
        let oa = oa.borrow();
        oa.as_ref()
            .map(|admin| assert!(admin == &caller(), "Only order admin can add orders"));
    });
    ORDER_BOOK.with(|ob| {
        ob.borrow_mut()
            .as_mut()
            .expect("Order book not initialized")
            .add_order(order)
    })
}

#[derive(CandidType)]
pub struct GetBookResult {
    pub bids: Vec<Order>,
    pub asks: Vec<Order>,
}

#[query]
pub fn get_book() -> GetBookResult {
    ORDER_BOOK.with(|ob| {
        let ob = ob.borrow();
        GetBookResult {
            bids: ob.as_ref().expect("Order book not initialized").list_bids(),
            asks: ob.as_ref().expect("Order book not initialized").list_asks(),
        }
    })
}

export_candid!();
