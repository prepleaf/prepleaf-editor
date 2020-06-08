import React from 'react';
const { useEffect, useRef, useState } = React;

class ImageBlock extends React.Component {
	constructor(props, context) {
		super(props, context);
		let editMode = !props.contentState
			.getEntity(this.props.block.getEntityAt(0))
			.getData()['url'];
		this.fileToUpload = props.contentState
			.getEntity(this.props.block.getEntityAt(0))
			.getData().file;
		if (this.fileToUpload) {
			editMode = false;
		}
		this.state = {
			editMode,
			image: '',
			uploadOnMount: !!this.fileToUpload,
		};
	}

	componentDidMount() {
		if (this.state.editMode) {
			this.inputRef && this.inputRef.click();
		}
		if (this.state.uploadOnMount) {
			this.uploadImage(this.fileToUpload);
		}
		let self = this;
		this.reader = new FileReader();
		this.reader.addEventListener(
			'load',
			function (result) {
				self.save(result.srcElement['result']);
			},
			false
		);
	}

	componentDidUpdate() {
		console.log({
			imageData: this.props.contentState
				.getEntity(this.props.block.getEntityAt(0))
				.getData(),
		});
	}

	handleClick = (e) => {
		if (this.state.editMode) {
			return;
		}
		this.setState(
			{
				editMode: true,
				url: this.props.contentState
					.getEntity(this.props.block.getEntityAt(0))
					.getData()['url'],
			},
			this.startEdit
		);
	};

	finishEdit = (newContentState) => {
		this.props.blockProps.onFinishEdit(
			this.props.block.getKey(),
			newContentState
		);
	};
	startEdit = () => {
		this.props.blockProps.onStartEdit(this.props.block.getKey());
	};

	handleSaveClick = (e) => {
		if (this.file) {
			this.uploadImage(this.file);
		}
	};

	save = (url) => {
		var entityKey = this.props.block.getEntityAt(0);
		var newContentState = this.props.contentState.mergeEntityData(entityKey, {
			url: url,
			file: undefined,
		});
		console.log(newContentState.toObject());
		this.setState(
			{
				editMode: false,
				url: null,
			},
			this.finishEdit.bind(this, newContentState)
		);
	};

	cancel = (e) => {
		this.setState(
			{
				editMode: false,
				url: null,
			},
			() => this.finishEdit(this.props.contentState)
		);
	};
	remove = (e) => {
		this.props.blockProps.onRemove(this.props.block.getKey());
	};
	handleFileChange = (e) => {
		this.file = e.target.files && e.target.files[0] ? e.target.files[0] : null;
		if (this.file) {
			this.handleSaveClick();
		}
	};
	randomName = () => {
		function makeid() {
			var text = '';
			var possible =
				'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789';

			for (var i = 0; i < 5; i++)
				text += possible.charAt(Math.floor(Math.random() * possible.length));

			return text;
		}
		return makeid() + Date.now();
	};

	uploadImage = (file) => {
		const { getImagePolicy } = this.props.blockProps;
		this.setState({ isUploading: true });
		setTimeout(() => {
			getImagePolicy(file)
				.then(({ policy, success }) => {
					if (success) {
						const fullURL = policy.url + '/' + policy.fields.key;
						const formData = new FormData();
						Object.keys(policy.fields).forEach((key) => {
							const value = policy.fields[key];
							formData.append(key, value);
						});
						formData.append('file', file);
						fetch(policy.url, {
							method: 'POST',
							headers: {},
							body: formData,
						}).then(() => {
							this.save(fullURL);
							this.setState({ isUploading: false });
						});
					} else {
						this.setState({ isUploading: false });
						alert('Some error occurred while uploading image');
					}
				})
				.catch((error) => {
					this.setState({ isUploading: false });
					console.log(`error occurred`, error);
				});
		}, [2000]);
		// this.reader.readAsDataURL(file)
	};

	render() {
		const { editMode, isUploading } = this.state;
		const { readOnly } = this.props.blockProps;
		var url;
		if (editMode) {
			url = this.state.url;
		} else {
			url = this.props.contentState
				.getEntity(this.props.block.getEntityAt(0))
				.getData()['url'];
		}
		return (
			<div
				onClick={readOnly ? undefined : this.handleClick}
				style={{ cursor: 'default', textAlign: 'center' }}
			>
				{editMode ? (
					<div>
						<div>
							Click here to upload image
							<input
								ref={this.handleRef}
								onChange={this.handleFileChange}
								type="file"
								accept="image/*"
							/>
						</div>
						<div>
							<button disabled={isUploading} onClick={this.handleSaveClick}>
								{isUploading ? 'Saving...' : 'Save'}
							</button>
							<button onClick={this.cancel}>Cancel</button>
							<button onClick={this.remove}>Remove</button>
						</div>
					</div>
				) : null}
				<div>{url ? <img src={url} /> : <span>No image uploaded</span>}</div>
			</div>
		);
	}
	handleRef = (ref) => {
		this.inputRef = ref;
	};
}

export default ImageBlock;
