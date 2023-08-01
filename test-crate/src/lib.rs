#![allow(non_upper_case_globals, dead_code)]

use tls_codec::{TlsDeserializeBytes, TlsSerializeBytes, TlsSize};


/// Manual TLS Codec implementations
mod tls_codec_helper;

pub type Bytes = Vec<u8>;
pub type Secret = Bytes;
pub type Label = str;

/// Spec: `uint16 CipherSuite;`
pub type Ciphersuite = u16;

/// Not defined in spec.
pub type SignatureScheme = u16;

/// Spec: `opaque HPKEPublicKey<V>;`
pub type HpkePublicKey = Bytes;

/// Spec: `opaque SignaturePublicKey<V>;`
pub type SignaturePublicKey = Bytes;

/// Spec: `opaque HashReference<V>;`
pub type HashReference = Bytes;

/// Spec:
/// ```text
/// HashReference KeyPackageRef;
/// HashReference ProposalRef;
/// ```
pub type KeyPackageRef = HashReference;
pub type ProposalRef = HashReference;

/// Spec:
/// ```text
/// // See IANA registry for registered values
/// uint16 CredentialType;
/// ```
pub type CredentialType = u16;

/// Spec:
/// ```text
/// struct {
///     opaque cert_data<V>;
/// } Certificate;
/// ```
pub type Certificate = Bytes;

///
pub type Identity = Bytes;

#[derive(Clone, Debug, PartialEq, Eq, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
#[repr(u16)]
pub enum CredentialValue {
    #[tls_codec(discriminant = 1)]
    Basic(Identity),
    X509(Vec<Certificate>),
}

/// Spec:
/// ```text
/// struct {
///     CredentialType credential_type;
///     select (Credential.credential_type) {
///         case basic:
///             opaque identity<V>;
///
///         case x509:
///             Certificate certificates<V>;
///     };
/// } Credential;
/// ```
///
/// We only support basic credentials for now.
#[derive(Clone, Debug, PartialEq, Eq, TlsSerializeBytes, TlsSize)]
pub struct Credential {
    #[tls_codec(skip)]
    pub credential_type: CredentialType,
    pub value: CredentialValue,
}

/// Spec:
/// ```text
/// opaque application_id<V>;
/// ```
pub type ApplicationId = Bytes;

/// Spec:
/// ```text
/// enum {
///     reserved(0),
///     mls10(1),
///     (65535)
/// } ProtocolVersion;
#[derive(Clone, Debug, Copy, PartialEq, Eq, TlsSize, TlsSerializeBytes, TlsDeserializeBytes)]
#[repr(u16)]
pub enum ProtocolVersion {
    Mls10 = 1,
}

/// Spec:
/// ```text
/// enum {
///     reserved(0),
///     application(1),
///     proposal(2),
///     commit(3),
///     (255)
/// } ContentType;
/// ```
#[derive(Clone, Debug, Copy, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
#[repr(u8)]
pub enum ContentType {
    Application = 1,
    Proposal = 2,
    Commit = 3,
}

/// Spec:
/// ```text
/// enum {
///     reserved(0),
///     member(1),
///     external(2),
///     new_member_proposal(3),
///     new_member_commit(4),
///     (255)
/// } SenderType;
/// ```
#[derive(Clone, Debug, Copy, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
#[repr(u8)]
pub enum SenderType {
    Member = 1,
    External = 2,
    NewMemberProposal = 3,
    NewMemberCommit = 4,
}

#[derive(Clone, Debug, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
#[repr(u8)]
pub enum SenderValue {
    #[tls_codec(discriminant = 1)]
    Member(u32),
    External(u32),
    NewMemberCommit,
    NewMemberProposal,
}

/// Spec:
/// ```text
/// struct {
///     SenderType sender_type;
///     select (Sender.sender_type) {
///         case member:
///             uint32 leaf_index;
///         case external:
///             uint32 sender_index;
///         case new_member_commit:
///         case new_member_proposal:
///             struct{};
///     }
/// } Sender;
/// ```
#[derive(Clone, Debug, TlsSerializeBytes, TlsSize)]
pub struct Sender {
    #[tls_codec(skip)]
    pub sender_type: SenderType,
    pub value: SenderValue,
}

/// Spec:
/// ```text
/// // See IANA registry for registered values
/// uint16 WireFormat;
/// ```
pub type WireFormat = u16;

pub type GroupEpoch = u64;

#[derive(Clone, Debug, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
#[repr(u8)]
pub enum FramedContentBody {
    #[tls_codec(discriminant = 1)]
    Application(Bytes),
    Proposal(Proposal),
    Commit(Commit),
}

/// Spec:
/// ```text
/// struct {
///     opaque group_id<V>;
///     uint64 epoch;
///     Sender sender;
///     opaque authenticated_data<V>;
///
///     ContentType content_type;
///     select (FramedContent.content_type) {
///         case application:
///           opaque application_data<V>;
///         case proposal:
///           Proposal proposal;
///         case commit:
///           Commit commit;
///     };
/// } FramedContent;
/// ```
#[derive(Clone, Debug, TlsSerializeBytes, TlsSize)]
pub struct FramedContent {
    pub group_id: GroupId,
    pub epoch: GroupEpoch,
    pub sender: Sender,
    pub authenticated_data: Bytes,

    #[tls_codec(skip)]
    pub content_type: ContentType,
    pub body: FramedContentBody,
}

#[derive(Clone, Debug)]
pub enum FramedContentTBSSenderType {
    Member(GroupContext),
    NewMemberCommit(GroupContext),
    External,
    NewMemberProposal,
}

/// Spec:
/// ```text
/// struct {
///     ProtocolVersion version = mls10;
///     WireFormat wire_format;
///     FramedContent content;
///     select (FramedContentTBS.content.sender.sender_type) {
///         case member:
///         case new_member_commit:
///             GroupContext context;
///         case external:
///         case new_member_proposal:
///             struct{};
///     };
/// } FramedContentTBS;
/// ```
///
/// TLS encoding is implemented manually because of the weird structure
#[derive(Clone, Debug)]
pub struct FramedContentTBS {
    pub version: ProtocolVersion,
    pub wire_format: WireFormat,
    pub content: FramedContent,
    pub optional_context: FramedContentTBSSenderType,
}

/// Spec:
/// ```text
///
/// struct {
///    /* SignWithLabel(., "FramedContentTBS", FramedContentTBS) */
///    opaque signature<V>;
///    select (FramedContent.content_type) {
///        case commit:
///            /*
///              MAC(confirmation_key,
///                  GroupContext.confirmed_transcript_hash)
///            */
///            MAC confirmation_tag;
///        case application:
///        case proposal:
///            struct{};
///    };
///} FramedContentAuthData;
/// ```
///
/// Manual deserialization needed within FramedContent as we
/// don't have the content_type here.
#[derive(Debug, Clone, TlsSerializeBytes, TlsSize)]
pub struct FramedContentAuthData {
    pub signature: Signature,
    pub confirmation_tag: ConfirmationTag,
}

/// ```text
///     select (PublicMessage.content.sender.sender_type) {
///         case member:
///             MAC membership_tag;
///         case external:
///         case new_member_commit:
///         case new_member_proposal:
///             struct{};
///     };
/// ```
///
/// Manual TLS encoding.
#[derive(Clone, Debug)]
pub enum MembershipTag {
    Member(Mac),
    External,
    NewMemberCommit,
    NewMemberProposal,
}

/// ```text
/// struct {
///     FramedContent content;
///     FramedContentAuthData auth;
///     select (PublicMessage.content.sender.sender_type) {
///         case member:
///             MAC membership_tag;
///         case external:
///         case new_member_commit:
///         case new_member_proposal:
///             struct{};
///     };
/// } PublicMessage;
/// ```
///
/// Manual TLS decoding needed because of the tag and AuthData.
#[derive(Clone, Debug, TlsSerializeBytes, TlsSize)]
pub struct PublicMessage {
    pub content: FramedContent,
    pub auth: FramedContentAuthData,
    pub membership_tag: MembershipTag,
}
/// Spec:
/// ```text
/// struct {
///     opaque group_id<V>;
///     uint64 epoch;
///     ContentType content_type;
///     opaque authenticated_data<V>;
///     opaque encrypted_sender_data<V>;
///     opaque ciphertext<V>;
/// } PrivateMessage;
/// ```
#[derive(Clone, Debug, TlsSerializeBytes, TlsSize, TlsDeserializeBytes)]
pub struct PrivateMessage {
    group_id: GroupId,
    epoch: GroupEpoch,
    content_type: ContentType,
    authenticated_data: Bytes,
    encrypted_sender_data: Bytes,
    ciphertext: Bytes,
}

/// Spec:
/// ```text
/// struct {
///     GroupContext group_context;
///     Extension extensions<V>;
///     MAC confirmation_tag;
///     uint32 signer;
///     /* SignWithLabel(., "GroupInfoTBS", GroupInfoTBS) */
///     opaque signature<V>;
/// } GroupInfo;
/// ```
#[derive(Clone, Debug, TlsSerializeBytes, TlsSize, TlsDeserializeBytes)]
pub struct GroupInfo {
    group_context: GroupContext,
    extensions: Vec<Extension>,
    confirmation_tag: Mac,
    signer: LeafIndex,
    signature: Bytes,
}

#[derive(Clone, Debug, TlsSerializeBytes, TlsSize, TlsDeserializeBytes)]
#[repr(u16)]
pub enum MlsMessageBody {
    #[tls_codec(discriminant = 1)]
    /// Plaintext message
    PublicMessage(PublicMessage),

    /// Ciphertext message
    PrivateMessage(PrivateMessage),

    /// Welcome message
    Welcome(Welcome),

    /// Group information
    GroupInfo(GroupInfo),

    /// KeyPackage
    KeyPackage(KeyPackage),
}

/// Spec:
/// ```text
/// struct {
///     ProtocolVersion version = mls10;
///     WireFormat wire_format;
///     select (MLSMessage.wire_format) {
///         case mls_public_message:
///             PublicMessage public_message;
///         case mls_private_message:
///             PrivateMessage private_message;
///         case mls_welcome:
///             Welcome welcome;
///         case mls_group_info:
///             GroupInfo group_info;
///         case mls_key_package:
///             KeyPackage key_package;
///     };
/// } MLSMessage;
/// ```
#[derive(Clone, Debug, TlsSerializeBytes, TlsSize, TlsDeserializeBytes)]
pub struct MlsMessage {
    version: ProtocolVersion,
    #[tls_codec(skip)]
    wire_format: WireFormat,
    body: MlsMessageBody,
}

pub type GroupId = Bytes;

/// Spec: `uint64 epoch;`
pub type Epoch = u64;

/// Spec: `opaque authenticated_data<V>;`
pub type AuthenticatedData = Bytes;

/// Spec: `opaque application_data<V>;`
pub type ApplicationData = Bytes;

/// Spec:
/// ```text
/// // See IANA registry for registered values
/// uint16 ProposalType;
/// ```
pub type ProposalType = u16;

/// Spec:
/// ```text
/// // See IANA registry for registered values
/// uint16 ExtensionType;
/// ```
pub type ExtensionType = u16;

/// Spec: `opaque extension_data<V>;`
pub type ExtensionData = Bytes;

/// Spec:
/// ```text
/// struct {
///     ExtensionType extension_type;
///     opaque extension_data<V>;
/// } Extension;
/// ```
#[derive(Clone, Debug, PartialEq, Eq, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
pub struct Extension {
    pub extension_type: ExtensionType,
    pub extension_data: ExtensionData,
}

/// Spec:
/// ```text
/// struct {
///     HPKEPublicKey external_pub;
/// } ExternalPub;
/// ```
#[derive(Clone, Debug, PartialEq, Eq, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
pub struct ExternalPub {
    external_pub: HpkePublicKey,
}

/// Spec:
/// ```text
/// struct {
///     ProtocolVersion versions<V>;
///     CipherSuite ciphersuites<V>;
///     ExtensionType extensions<V>;
///     ProposalType proposals<V>;
///     CredentialType credentials<V>;
/// } Capabilities;
/// ```
#[derive(Clone, Debug, PartialEq, Eq, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
pub struct Capabilities {
    pub versions: Vec<ProtocolVersion>,
    pub ciphersuites: Vec<Ciphersuite>,
    pub extensions: Vec<ExtensionType>,
    pub proposals: Vec<ProposalType>,
    pub credentials: Vec<CredentialType>,
}

/// Spec:
/// ```text
/// enum {
///     reserved(0),
///     key_package(1),
///     update(2),
///     commit(3),
///     (255)
/// } LeafNodeSource;
/// ```
#[derive(Clone, Debug, Copy, PartialEq, Eq, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
#[repr(u8)]
pub enum LeafNodeSourceType {
    KeyPackage = 1,
    Update = 2,
    Commit = 3,
}

/// Spec:
/// ```text
/// struct {
///     uint64 not_before;
///     uint64 not_after;
/// } Lifetime;
/// ```
#[derive(Clone, Debug, Copy, PartialEq, Eq, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
pub struct Lifetime {
    pub not_before: u64,
    pub not_after: u64,
}

/// Spec: ` opaque parent_hash<V>;`
pub type ParentHash = Bytes;

#[derive(Clone, Debug, PartialEq, Eq, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
#[repr(u8)]
pub enum LeafNodeSourceValue {
    #[tls_codec(discriminant = 1)]
    KeyPackage(Lifetime),
    Update,
    Commit(ParentHash),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LeafNodeSourceGroupId {
    KeyPackage,
    Update(GroupId),
    Commit(GroupId),
}

/// This struct does not exist in MLS but is a helper for TLS encodings and
/// simplifying the code.
///
/// ```text
/// struct {
///     HPKEPublicKey encryption_key;
///     SignaturePublicKey signature_key;
///     Credential credential;
///     Capabilities capabilities;
///
///     LeafNodeSource leaf_node_source;
///     select (LeafNodeBody.leaf_node_source) {
///         case key_package:
///             Lifetime lifetime;
///
///         case update:
///             struct{};
///
///         case commit:
///             opaque parent_hash<V>;
///     }
///
///     Extension extensions<V>;
/// } LeafNodeBody;
/// ```
///
/// Note that `leaf_node_source` is encoded in `leaf_node_source_value` here.
#[derive(Clone, Debug, PartialEq, Eq, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
pub struct LeafNodeBody {
    pub encryption_key: HpkePublicKey,
    pub signature_key: SignaturePublicKey,
    pub credential: Credential,
    pub capabilities: Capabilities,
    pub leaf_node_source_value: LeafNodeSourceValue,
    pub extensions: Vec<Extension>,
}

#[derive(Clone, Debug, TlsSerializeBytes, TlsSize)]
pub struct LeafNodeSourceTbsValue {
    pub group_id: Bytes,
    pub leaf_index: u32,
}

#[derive(Clone, Debug, TlsSerializeBytes, TlsSize)]
#[repr(u8)]
pub enum LeafNodeSourceTbs {
    KeyPackage,
    Update(LeafNodeSourceTbsValue),
    Commit(LeafNodeSourceTbsValue),
}

/// Spec:
/// ```text
/// struct {
///     HPKEPublicKey encryption_key;
///     SignaturePublicKey signature_key;
///     Credential credential;
///     Capabilities capabilities;
///
///     LeafNodeSource leaf_node_source;
///     select (LeafNodeTBS.leaf_node_source) {
///         case key_package:
///             Lifetime lifetime;
///
///         case update:
///             struct{};
///
///         case commit:
///             opaque parent_hash<V>;
///     }
///
///     Extension extensions<V>;
///
///     select (LeafNodeTBS.leaf_node_source) {
///         case key_package:
///             struct{};
///     
///         case update:
///             opaque group_id<V>;
///             uint32 leaf_index;
///     
///         case commit:
///             opaque group_id<V>;
///             uint32 leaf_index;
///     };
/// } LeafNodeTBS;
/// ```
///
/// This is implemented as follows here
///
/// ```text
/// struct {
///     LeafNodeBody body;
///
///     select (LeafNodeTBS.leaf_node_source) {
///         case key_package:
///             struct{};
///     
///         case update:
///             opaque group_id<V>;
///             uint32 leaf_index;
///     
///         case commit:
///             opaque group_id<V>;
///             uint32 leaf_index;
///     };
/// } LeafNodeTBS;
/// ```
///
/// This needs manual TLS encoding.
#[derive(Clone, Debug)]
pub struct LeafNodeTbs {
    pub body: LeafNodeBody,
    pub group_idx: LeafNodeSourceTbs,
}

/// Spec:
/// ```text
/// struct {
///     HPKEPublicKey encryption_key;
///     SignaturePublicKey signature_key;
///     Credential credential;
///     Capabilities capabilities;
///
///     LeafNodeSource leaf_node_source;
///     select (LeafNode.leaf_node_source) {
///         case key_package:
///             Lifetime lifetime;
///
///         case update:
///             struct{};
///
///         case commit:
///             opaque parent_hash<V>;
///     }
///
///     Extension extensions<V>;
///     // SignWithLabel(., "LeafNodeTBS", LeafNodeTBS)
///     opaque signature<V>;
/// } LeafNode;
/// ```
///
/// This is implemented here as follows
///
/// ```text
/// struct {
///     LeafNodeBody body;
///     // SignWithLabel(., "LeafNodeTBS", LeafNodeTBS)
///     opaque signature<V>;
/// } LeafNode;
/// ```
#[derive(Clone, Debug, PartialEq, Eq, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
pub struct LeafNode {
    pub body: LeafNodeBody,
    pub signature: Signature,
}

/// Spec:
/// ```text
/// struct {
///     ProtocolVersion version;
///     CipherSuite cipher_suite;
///     HPKEPublicKey init_key;
///     LeafNode leaf_node;
///     Extension extensions<V>;
/// } KeyPackageTBS;
/// ```
#[derive(Clone, Debug, PartialEq, Eq, TlsSize, TlsSerializeBytes, TlsDeserializeBytes)]
pub struct KeyPackageTBS {
    pub version: ProtocolVersion,
    pub cipher_suite: Ciphersuite,
    pub init_key: HpkePublicKey,
    pub leaf_node: LeafNode,
    pub extensions: Vec<Extension>,
}

/// Spec: `opaque signature<V>;`
pub type Signature = Bytes;

/// Spec:
/// ```text
/// struct {
///     ProtocolVersion version;
///     CipherSuite cipher_suite;
///     HPKEPublicKey init_key;
///     LeafNode leaf_node;
///     Extension extensions<V>;
///     // SignWithLabel(., "KeyPackageTBS", KeyPackageTBS)
///     opaque signature<V>;
/// } KeyPackage;
/// ```
#[derive(Clone, Debug, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
pub struct KeyPackage {
    pub version: ProtocolVersion,
    pub cipher_suite: Ciphersuite,
    pub init_key: HpkePublicKey,
    pub leaf_node: LeafNode,
    pub extensions: Vec<Extension>,
    pub signature: Signature,
}

/// Spec:
/// ```text
/// struct {
///     KeyPackage key_package;
/// } Add;
/// ```
#[derive(Debug, Clone, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
pub struct Add {
    pub key_package: KeyPackage,
}

/// Spec:
/// ```text
/// struct {
///     LeafNode leaf_node;
/// } Update;
/// ```
#[derive(Debug, Clone, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
pub struct Update {
    pub leaf_node: LeafNode,
}

/// Spec:
/// ```text
/// struct {
///     uint32 removed;
/// } Remove;
/// ```
#[derive(Debug, Clone, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
pub struct Remove {
    pub removed: u32,
}

/// Spec:
/// ```text
/// enum {
///   reserved(0),
///   external(1),
///   resumption(2),
///   (255)
/// } PSKType;
/// ```
#[derive(Debug, Clone, Copy, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
#[repr(u8)]
pub enum PskType {
    External = 1,
    Resumption = 2,
}

/// Spec:
/// ```text
/// enum {
///   reserved(0),
///   application(1),
///   reinit(2),
///   branch(3),
///   (255)
/// } ResumptionPSKUsage;
/// ```
#[derive(Debug, Clone, Copy, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
#[repr(u8)]
pub enum ResumptionPskUsage {
    Application = 1,
    ReInit = 2,
    Branch = 3,
}

pub type PskGroupId = Bytes;

/// ```text
///   select (PreSharedKeyID.psktype) {
///     case external:
///       opaque psk_id<V>;
///
///     case resumption:
///       ResumptionPSKUsage usage;
///       opaque psk_group_id<V>;
///       uint64 psk_epoch;
///   }
/// ```
#[derive(Debug, Clone, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
#[repr(u8)]
pub enum PskValue {
    #[tls_codec(discriminant = 1)]
    External { psk_id: Bytes },
    Resumption {
        usage: ResumptionPskUsage,
        psk_group_id: PskGroupId,
        psk_epoch: Epoch,
    },
}

/// Spec: `opaque psk_nonce<V>;`
pub type PskNonce = Bytes;

/// Spec:
/// ```text
/// struct {
///   PSKType psktype;
///   select (PreSharedKeyID.psktype) {
///     case external:
///       opaque psk_id<V>;
///
///     case resumption:
///       ResumptionPSKUsage usage;
///       opaque psk_group_id<V>;
///       uint64 psk_epoch;
///   }
///   opaque psk_nonce<V>;
/// } PreSharedKeyID;
/// ```
#[derive(Debug, Clone, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
pub struct PreSharedKeyID {
    pub psktype: PskType,
    pub value: PskValue,
    pub pks_nonce: Vec<PskNonce>,
}

/// Spec:
/// ```text
/// struct {
///     PreSharedKeyID id;
///     uint16 index;
///     uint16 count;
/// } PSKLabel;
/// ```
#[derive(Debug, Clone)]
pub struct PskLabel {
    pub id: PreSharedKeyID,
    pub index: u16,
    pub count: u16,
}

/// Spec:
/// ```text
/// struct {
///     PreSharedKeyID psk;
/// } PreSharedKey;
/// ```
#[derive(Debug, Clone, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
pub struct PreSharedKey {
    psk: PreSharedKeyID,
}

/// Spec:
/// ```text
/// struct {
///   opaque kem_output<V>;
/// } ExternalInit;
/// ```
#[derive(Debug, Clone, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
pub struct ExternalInit {
    pub kem_output: Bytes,
}

/// Spec:
/// ```text
/// struct {
///   Extension extensions<V>;
/// } GroupContextExtensions;
/// ```
#[derive(Debug, Clone, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
pub struct GroupContextExtensions {
    pub extensions: Vec<Extension>,
}

/// Spec:
/// ```text
/// struct {
///     opaque group_id<V>;
///     ProtocolVersion version;
///     CipherSuite cipher_suite;
///     Extension extensions<V>;
/// } ReInit;
/// ```
#[derive(Debug, Clone, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
pub struct ReInit {
    pub group_id: GroupId,
    pub version: ProtocolVersion,
    pub cipher_suite: Ciphersuite,
    pub extensions: Vec<Extension>,
}

/// Spec:
/// ```text
/// struct {
///     ProposalType msg_type;
///     select (Proposal.msg_type) {
///         case add:                      Add;
///         case update:                   Update;
///         case remove:                   Remove;
///         case psk:                      PreSharedKey;
///         case reinit:                   ReInit;
///         case external_init:            ExternalInit;
///         case group_context_extensions: GroupContextExtensions;
///     };
/// } Proposal;
/// ```
#[derive(Debug, Clone, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
#[repr(u16)]
pub enum Proposal {
    #[tls_codec(discriminant = 1)]
    Add(Add),
    Update(Update),
    Remove(Remove),
    Psk(PreSharedKey),
    ReInit(ReInit),
    ExternalInit(ExternalInit),
    GroupContextExtensions(GroupContextExtensions),
}

// #[derive(Debug, Clone, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
// pub struct Proposal {
//     pub msg_type: ProposalType,
//     pub value: ProposalValue,
// }

/// Spec:
/// ```text
/// enum {
///   reserved(0),
///   proposal(1)
///   reference(2),
///   (255)
/// } ProposalOrRefType;
/// ```
#[derive(Debug, Clone, Copy, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
#[repr(u8)]
pub enum ProposalOrRefType {
    Proposal = 1,
    Reference = 2,
}

#[derive(Debug, Clone, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
#[repr(u8)]
pub enum ProposalOrRefValue {
    #[tls_codec(discriminant = 1)]
    Proposal(Proposal),
    Reference(ProposalRef),
}

/// Spec:
/// ```text
/// struct {
///   ProposalOrRefType type;
///   select (ProposalOrRef.type) {
///     case proposal:  Proposal proposal;
///     case reference: ProposalRef reference;
///   }
/// } ProposalOrRef;
/// ```
#[derive(Debug, Clone, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
pub struct ProposalOrRef {
    pub por_type: ProposalOrRefType,
    pub value: ProposalOrRefValue,
}

/// Spec:
/// ```text
/// struct {
///     ProposalOrRef proposals<V>;
///     optional<UpdatePath> path;
/// } Commit;
/// ```
#[derive(Debug, Clone, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
pub struct Commit {
    pub proposals: Vec<ProposalOrRef>,
    pub path: Option<UpdatePath>,
}

#[derive(Debug, Clone)]
pub enum ContentValue {
    Application(ApplicationData),
    Proposal(Proposal),
    Commit(Commit),
}

/// Spec:
/// ```text
/// struct {
///     opaque group_id<V>;
///     uint64 epoch;
///     Sender sender;
///     opaque authenticated_data<V>;
///
///     ContentType content_type;
///     select (MLSContent.content_type) {
///         case application:
///           opaque application_data<V>;
///         case proposal:
///           Proposal proposal;
///         case commit:
///           Commit commit;
///     }
/// } MLSContent;
/// ```
#[derive(Clone, Debug)]
pub struct MlsContent(
    pub GroupId,
    pub Epoch,
    pub Sender,
    pub AuthenticatedData,
    pub ContentType,
    pub ContentValue,
);

/// Spec:
/// ```text
/// enum {
///     reserved(0),
///     leaf(1),
///     parent(2),
///     (255)
/// } NodeType;
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum NodeType {
    Leaf = 1,
    Parent = 2,
}

/// Spec: `opaque MAC<V>;`
pub type Mac = Bytes;

/// ```text
/// select (FramedContent.content_type) {
///     case commit:
///         /*
///           MAC(confirmation_key,
///               GroupContext.confirmed_transcript_hash)
///         */
///         MAC confirmation_tag;
///     case application:
///     case proposal:
///         struct{};
/// };
/// ```
///
/// Manuel TLS encoding needed.
#[derive(Debug, Clone)]
pub enum ConfirmationTag {
    Commit(Mac),
    Application,
    Proposal,
}

/// Spec:
/// ```text
/// struct {
///     MAC confirmation_tag;
/// } InterimTranscriptHashInput;
/// ```
#[derive(Clone, Debug)]
pub struct InterimTranscriptHashInput(pub Mac);

/// Spec:
/// ```text
/// struct {
///     WireFormat wire_format;
///     MLSContent content; // with content.content_type == commit
///     opaque signature<V>;
/// } ConfirmedTranscriptHashInput;
/// ```
#[derive(Clone, Debug)]
pub struct ConfirmedTranscriptHashInput(pub WireFormat, pub MlsContent, pub Signature);

/// Spec: `opaque confirmed_transcript_hash<V>;`
pub type ConfirmedTranscriptHash = Bytes;

/// Spec: `opaque tree_hash<V>;`
pub type TreeHash = Bytes;

/// Spec:
/// ```text
/// struct {
///     ProtocolVersion version = mls10;
///     CipherSuite cipher_suite;
///     opaque group_id<V>;
///     uint64 epoch;
///     opaque tree_hash<V>;
///     opaque confirmed_transcript_hash<V>;
///     Extension extensions<V>;
/// } GroupContext;
/// ```
#[derive(Clone, Debug, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
pub struct GroupContext {
    pub version: ProtocolVersion,
    pub cipher_suite: Ciphersuite,
    pub group_id: GroupId,
    pub epoch: Epoch,
    pub tree_hash: TreeHash,
    pub confirmed_transcript_hash: ConfirmedTranscriptHash,
    pub extensions: Vec<Extension>,
}

#[derive(Clone, Debug)]
pub enum MlsContentContext {
    Member(GroupContext),
    NewMemberCommit(GroupContext),
    External(),
    NewMemberProposal(),
}

/// Spec:
/// ```text
/// struct {
///     ProtocolVersion version = mls10;
///     WireFormat wire_format;
///     MLSContent content;
///     select (MLSContentTBS.content.sender.sender_type) {
///         case member:
///         case new_member_commit:
///             GroupContext context;
///         case external:
///         case new_member_proposal:
///             struct{};
///     }
/// } MLSContentTBS;
/// ```
#[derive(Clone, Debug)]
pub struct MlsContentTbs(
    pub ProtocolVersion,
    pub WireFormat,
    pub MlsContent,
    pub MlsContentContext,
);

/// Spec:
/// ```text
/// struct {
///   FramedContentTBS content_tbs;
///   FramedContentAuthData auth;
/// } AuthenticatedContentTBM;
/// ```
#[derive(Clone)]
pub struct AuthenticatedContentTBM {
    content_tbs: FramedContentTBS,
    auth: FramedContentAuthData,
}

/// Spec: `uint32 leaf_index;
pub type LeafIndex = u32;

/// Spec: `uint32 generation;`
pub type Generation = u32;

// Spec: `opaque reuse_guard[4];`
pub type ReuseGuard = [u8; 4];

/// Spec:
/// ```text
/// struct {
///     uint32 leaf_index;
///     uint32 generation;
///     opaque reuse_guard[4];
/// } SenderData;
/// ```
#[derive(Clone, Debug)]
pub struct SenderData {
    leaf_index: LeafIndex,
    generation: Generation,
    reuse_guard: ReuseGuard,
}

/// Spec:
/// ```text
/// struct {
///     opaque group_id<V>;
///     uint64 epoch;
///     ContentType content_type;
/// } MLSSenderDataAAD;
/// ```
#[derive(Clone, Debug)]
pub struct MlsSenderDataAad(pub GroupId, pub Epoch, pub ContentType);

/// Spec: `opaque encrypted_sender_data<V>;`
pub type EncryptedSenderData = Bytes;

/// Spec: `opaque ciphertext<V>;`
pub type Ciphertext = Bytes;

/// Spec:
/// ```text
/// struct {
///     opaque group_id<V>;
///     uint64 epoch;
///     ContentType content_type;
///     opaque authenticated_data<V>;
///     opaque encrypted_sender_data<V>;
///     opaque ciphertext<V>;
/// } MLSCiphertext;
/// ```
#[derive(Clone, Debug)]
pub struct MlsCiphertext(
    pub GroupId,
    pub Epoch,
    pub ContentType,
    pub AuthenticatedData,
    pub EncryptedSenderData,
    pub Ciphertext,
);

#[derive(Clone, Debug)]
pub enum MlsCiphertextContentValue {
    Application(ApplicationData),
    Proposal(Proposal),
    Commit(Commit),
}

/// Spec: `opaque padding[length_of_padding];`
pub type Padding = Bytes;

/// Spec: `opaque kem_output<V>;`
pub type KemOutput = Bytes;

/// Spec:
/// ```text
/// struct {
///     opaque kem_output<V>;
///     opaque ciphertext<V>;
/// } HPKECiphertext;
/// ```
#[derive(Clone, Debug, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
pub struct HpkeCiphertext {
    pub kem_output: KemOutput,
    pub ciphertext: Ciphertext,
}

/// Spec: `opaque joiner_secret<V>;`
pub type JoinerSecret = Bytes;

/// Spec:
/// ```text
/// struct {
///   opaque joiner_secret<V>;
///   optional<PathSecret> path_secret;
///   PreSharedKeyID psks<V>
/// } GroupSecrets;
/// ```
#[derive(Clone, Debug)]
pub struct GroupSecrets(
    pub JoinerSecret,
    pub Option<PathSecret>,
    pub Vec<PreSharedKeyID>,
);

/// Spec:
/// ```text
/// struct {
///   KeyPackageRef new_member;
///   HPKECiphertext encrypted_group_secrets;
/// } EncryptedGroupSecrets;
/// ```
#[derive(Clone, Debug, TlsSerializeBytes, TlsSize, TlsDeserializeBytes)]
pub struct EncryptedGroupSecrets {
    new_member: KeyPackageRef,
    encrypted_group_secrets: HpkeCiphertext,
}

/// Spec: `opaque encrypted_group_info<V>;`
pub type EncryptedGroupInfo = Bytes;

/// Spec:
/// ```text
/// struct {
///   CipherSuite cipher_suite;
///   EncryptedGroupSecrets secrets<V>;
///   opaque encrypted_group_info<V>;
/// } Welcome;
/// ```
#[derive(Clone, Debug, TlsSerializeBytes, TlsSize, TlsDeserializeBytes)]
pub struct Welcome(
    pub Ciphersuite,
    pub Vec<EncryptedGroupSecrets>,
    pub EncryptedGroupInfo,
);

/// Spec: `uint32 signer;`
pub type Signer = u32;

/// Spec:
/// ```text
/// struct {
///     GroupContext group_context;
///     Extension extensions<V>;
///     MAC confirmation_tag;
///     uint32 signer;
/// } GroupInfoTBS;
/// ```
#[derive(Clone, Debug)]
pub struct GroupInfoTBS {
    group_context: GroupContext,
    extensions: Vec<Extension>,
    confirmation_tag: Mac,
    signer: Signer,
}

/// Spec: `uint32 unmerged_leaves<V>;`
pub type UnmergedLeaves = Vec<u32>;

/// Spec:
/// ```text
/// struct {
///     HPKEPublicKey encryption_key;
///     opaque parent_hash<V>;
///     uint32 unmerged_leaves<V>;
/// } ParentNode;
/// ```
#[derive(Clone, Debug, PartialEq, Eq, TlsSize, TlsDeserializeBytes, TlsSerializeBytes)]
pub struct ParentNode {
    pub encryption_key: HpkePublicKey,
    pub parent_hash: ParentHash,
    pub unmerged_leaves: UnmergedLeaves,
}

/// Spec:
/// ```text
/// struct {
///   opaque path_secret<V>;
/// } PathSecret;
/// ```
#[derive(Clone, Debug)]
pub struct PathSecret {
    pub path_secret: Bytes,
}

/// Spec:
/// ```text
/// struct {
///     HPKEPublicKey encryption_key;
///     HPKECiphertext encrypted_path_secret<V>;
/// } UpdatePathNode;
/// ```
#[derive(Clone, Debug, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
pub struct UpdatePathNode {
    pub encryption_key: HpkePublicKey,
    pub encrypted_path_secret: Vec<HpkeCiphertext>,
}

/// Spec:
/// ```text
/// struct {
///     LeafNode leaf_node;
///     UpdatePathNode nodes<V>;
/// } UpdatePath;
/// ```
#[derive(Clone, Debug, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
pub struct UpdatePath {
    pub leaf_node: LeafNode,
    pub nodes: Vec<UpdatePathNode>,
}

/// Spec:
/// ```text
/// struct {
///     uint32 leaf_index;
///     optional<LeafNode> leaf_node;
/// } LeafNodeHashInput;
/// ```
#[derive(Clone, Debug, PartialEq, Eq, TlsSize, TlsSerializeBytes, TlsDeserializeBytes)]
pub struct LeafNodeHashInput {
    pub leaf_index: LeafIndex,
    pub leaf_node: Option<LeafNode>,
}

/// Spec: `opaque left_hash<V>;`
pub type LeftHashValue = Bytes;

/// Spec: `opaque right_hash<V>;`
pub type RightHashValue = Bytes;

/// Spec:
/// ```text
/// struct {
///     optional<ParentNode> parent_node;
///     opaque left_hash<V>;
///     opaque right_hash<V>;
/// } ParentNodeHashInput;
/// ```
#[derive(Clone, Debug, PartialEq, Eq, TlsSize, TlsSerializeBytes, TlsDeserializeBytes)]
pub struct ParentNodeHashInput {
    pub parent_node: Option<ParentNode>,
    pub left_hash: LeftHashValue,
    pub right_hash: RightHashValue,
}

#[derive(Clone, Debug, PartialEq, Eq, TlsSize, TlsSerializeBytes, TlsDeserializeBytes)]
#[repr(u8)]
pub enum TreeHashInputValue {
    #[tls_codec(discriminant = 1)]
    Leaf(LeafNodeHashInput),
    Parent(ParentNodeHashInput),
}

/// Spec:
/// ```text
/// struct {
///   NodeType node_type;
///   select (TreeHashInput.node_type) {
///     case leaf:   LeafNodeHashInput leaf_node;
///     case parent: ParentNodeHashInput parent_node;
///   }
/// } TreeHashInput;
/// ```
///
/// Note that we skip the `node_type` in the implementation because it is implicit
/// in the value.
#[derive(Clone, Debug, PartialEq, Eq, TlsSize, TlsSerializeBytes, TlsDeserializeBytes)]
pub struct TreeHashInput {
    pub value: TreeHashInputValue,
}

/// Spec: `opaque original_sibling_tree_hash<V>;`
pub type OriginalSiblingTreeHash = Bytes;

/// Spec:
/// ```text
/// struct {
///     HPKEPublicKey encryption_key;
///     opaque parent_hash<V>;
///     opaque original_sibling_tree_hash<V>;
/// } ParentHashInput;
/// ```
#[derive(Debug, Clone, PartialEq, Eq, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
pub struct ParentHashInput {
    pub encryption_key: HpkePublicKey,
    pub parent_hash: ParentHash,
    pub original_sibling_tree_hash: OriginalSiblingTreeHash,
}

/// Spec: `opaque context<V> = Context;`
pub type KdfLabelContext = Bytes;

/// Spec: `opaque label<V> = "MLS 1.0 " + Label;`
pub type KdfLabelString = Bytes;

/// Spec:
/// ```text
/// struct {
///     uint16 length = Length;
///     opaque label<V> = "MLS 1.0 " + Label;
///     opaque context<V> = Context;
/// } KDFLabel;
/// ```
#[derive(Debug, Clone, PartialEq, Eq, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
pub struct KdfLabel {
    pub length: u16,
    pub label: KdfLabelString,
    pub context: KdfLabelContext,
}

/// Spec:
/// ```text
/// struct {
///     opaque label<V>;
///     opaque content<V>;
/// } SignContent;
/// ```
///
/// with
///
/// ```text
/// label = "MLS 1.0 " + Label;
/// content = Content;
/// ```
#[derive(Debug, Clone, TlsSize, TlsSerializeBytes)]
pub struct SignContent {
    pub label: Bytes,
    pub content: Bytes,
}

impl SignContent {
    pub fn new(label_in: Bytes, content: Bytes) -> Self {
        let mut label = b"MLS 1.0 ".to_vec();
        label.extend_from_slice(&label_in);

        Self { label, content }
    }
}

/// Spec:
/// ```text
/// struct {
///     ExtensionType extension_types<V>;
///     ProposalType proposal_types<V>;
///     CredentialType credential_types<V>;
/// } RequiredCapabilities;
/// ```
#[derive(Debug, Clone)]
pub struct RequiredCapabilities(
    pub Vec<ExtensionType>,
    pub Vec<ProposalType>,
    pub Vec<CredentialType>,
);

#[derive(Debug, Clone, PartialEq, Eq, TlsSize, TlsSerializeBytes, TlsDeserializeBytes)]
#[repr(u8)]
pub enum NodeValue {
    #[tls_codec(discriminant = 1)]
    Leaf(LeafNode),
    ParentNode(ParentNode),
}

/// Spec:
/// ```text
/// struct {
///     NodeType node_type;
///     select (Node.node_type) {
///         case leaf:   LeafNode leaf_node;
///         case parent: ParentNode parent_node;
///     };
/// } Node;
/// ```
///
/// Note that the `node_type` is skipped in the implementation here because it is
/// implicitly given by the `value`.
#[derive(Debug, Clone, PartialEq, Eq, TlsSize, TlsSerializeBytes, TlsDeserializeBytes)]
pub struct Node {
    // pub node_type: NodeType,
    pub value: NodeValue,
}

/// Spec: `optional<Node> ratchet_tree<V>;`
pub type RatchetTree = Vec<Option<Node>>;
